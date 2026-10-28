import Lowering.LIRSim
import Lowering.AllocRun

/-!
# Lowering — the print's forward simulation  `[spec §56]`

A run of the source machine under the LIR's allocator (`bumpAlloc`) to a value is followed by
the interpreter on the print: at every fuel the interpreter answers the corresponding value or
runs out of fuel, and from some fuel on it answers. The source's host is the interpreter's,
`lirHost`.

- **Values** correspond (`VRel`): `()`, literals as their words, a location as the same address,
  pairs and injections componentwise, a `λ` as the closure of its code with its captured slots'
  values in its environment, a primitive as the closure of its code, and `store v` as the closure
  of `store1Code` on `v`'s.
- **Memories** correspond (`HRel`): the source's cells are the LIR's live addresses, each an
  object of one address holding a corresponding value, every one below the next region base, at
  which the LIR's `next` stands after as many allocations as the source's count.
- **Frames.** While a term runs, the print's variable `ρ k` holds the value of each slot `k` it
  reads or the rest reads (`need`, `FrameOK`); the term consumes exactly the slots it reads and
  the rest does not (`cons`), and leaves every other variable as it was (`Post`).
- **The interpreter's checks**: a `copy` or `drop` is at a variable whose type is `unit`
  (`tyTable`), so it passes the type checks; the print writes no `load`.
-/

namespace Lowering
open BoCa
open BoCa.BoLo (Heap Head Step1 Steps Kont Alloc AHead)
open Backend2 (Var Tm Fn Code CodeKind Prog LTy LCTy Op LV St IM)

local instance : HostIs Backend2.lirHost := ⟨⟩

/-! ### Values and memories -/

/-- **The correspondence of values.** -/
inductive VRel (p : Prog) (N : Nat) : Val → LV → Prop where
  | unit : VRel p N Val.unit .unit
  | lit (c : IntLit) : VRel p N (Val.prim (.lit c)) (Backend2.litV c)
  | loc (ℓ : Loc) : VRel p N (Val.loc ℓ) (.loc ℓ)
  | pair {a b : Val} {x y : LV} (ha : VRel p N a x) (hb : VRel p N b y) :
      VRel p N (Val.pair a b) (.pair x y)
  | inj₁ {a : Val} {x : LV} (ha : VRel p N a x) : VRel p N (Val.inj₁ a) (.inj false x)
  | inj₂ {a : Val} {x : LV} (ha : VRel p N a x) : VRel p N (Val.inj₂ a) (.inj true x)
  | host (op : HostOp) (c : Nat) (h : CodeAt p c 0 (hostFn op)) :
      VRel p N (Val.prim (.host op)) (.clos c [])
  | rt (q : Prim) (c : Nat) (h : rtCode q = some c) : VRel p N (Val.prim q) (.clos c [])
  | store1 {v : Val} {x : LV} (h : VRel p N v x) : VRel p N (Val.storeV v) (.clos store1Code [x])
  | lam {c m : Nat} {b : Expr} {tb : Tm} {γ : List Val} {env : List LV}
      (hpr : Pr p N (lamEnv b) ((capt b).length + 1) noOut b tb m) (hm : m ≤ N)
      (hc : CodeAt p c (capt b).length (dropIf (!mentions b 0) (capt b).length tb))
      (hlen : env.length = (capt b).length) (hcapl : ∀ k, k ∈ capt b → k < γ.length)
      (hrel : ∀ i (hi : i < env.length) (k : Nat) (hk : k < γ.length), (capt b)[i]? = some k →
        VRel p N γ[k] env[i]) :
      VRel p N (Val.lam (Expr.psub 1 γ b)) (.clos c env)

/-- **The correspondence of memories** at the source's allocation count `c`. -/
structure HRel (p : Prog) (N : Nat) (c : Nat) (μ : Heap) (s : St) : Prop where
  next : s.next = regionBase c
  dom : ∀ a, μ a = none ↔ s.mem[a]? = none
  val : ∀ a v, μ a = some v → ∃ x, s.mem[a]? = some (some x) ∧ VRel p N v x
  objs : ∀ a, s.objs[a]? = if μ a = none then none else some 1
  below : ∀ a, μ a ≠ none → a < regionBase c

theorem HRel.frame {p : Prog} {N c : Nat} {μ : Heap} {s : St} (h : HRel p N c μ s)
    (F : Std.HashMap Var LV) : HRel p N c μ ({ s with frame := F } : St) :=
  ⟨h.next, h.dom, h.val, h.objs, h.below⟩

/-! ### Slots and frames -/

/-- The slots `e` consumes: those it mentions that the rest does not read. -/
def cons (e : Expr) (out : Out) (k : Nat) : Bool := mentions e k && !out k

/-- **The frame holds the slots `S`**: every variable below `n`; at each slot of `S`, its
variable holds a value corresponding to the slot's, and `ρ` is one-to-one on `S`. -/
structure FrameOK (p : Prog) (N : Nat) (γ : List Val) (ρ : Nat → Nat) (n : Nat) (S : Nat → Bool)
    (F : Std.HashMap Var LV) : Prop where
  fresh : ∀ (x : Nat) v, F[x]? = some v → x < n
  live : ∀ k, S k = true → ∃ w v, γ[k]? = some w ∧ F[ρ k]? = some v ∧ VRel p N w v
  inj : ∀ k k', S k = true → S k' = true → ρ k = ρ k' → k = k'

/-- **What a run leaves of the frame**: the slots `C` are consumed, every other variable is as
it was. -/
def Post (C : Nat → Bool) (ρ : Nat → Nat) (F F' : Std.HashMap Var LV) : Prop :=
  (∀ k, C k = true → F'[ρ k]? = none) ∧
  (∀ x : Nat, (∀ k, C k = true → ρ k ≠ x) → F'[x]? = F[x]?)

theorem FrameOK.mono {p : Prog} {N : Nat} {γ : List Val} {ρ : Nat → Nat} {n m : Nat}
    {S S' : Nat → Bool} {F : Std.HashMap Var LV} (h : FrameOK p N γ ρ n S F) (hm : n ≤ m)
    (hS : ∀ k, S' k = true → S k = true) : FrameOK p N γ ρ m S' F :=
  ⟨fun x v hx => lt_of_lt_of_le (h.fresh x v hx) hm, fun k hk => h.live k (hS k hk),
    fun k k' hk hk' he => h.inj k k' (hS k hk) (hS k' hk') he⟩

theorem FrameOK.lt {p : Prog} {N : Nat} {γ : List Val} {ρ : Nat → Nat} {n : Nat}
    {S : Nat → Bool} {F : Std.HashMap Var LV} (h : FrameOK p N γ ρ n S F) {k : Nat}
    (hk : S k = true) : ρ k < n := by
  obtain ⟨_, v, _, hv, -⟩ := h.live k hk
  exact h.fresh _ _ hv

theorem FrameOK.congr {p : Prog} {N : Nat} {γ : List Val} {ρ : Nat → Nat} {n : Nat}
    {S : Nat → Bool} {F G : Std.HashMap Var LV} (h : FrameOK p N γ ρ n S F)
    (hG : ∀ x : Nat, G[x]? = F[x]?) : FrameOK p N γ ρ n S G :=
  ⟨fun x v hx => h.fresh x v (hG x ▸ hx), fun k hk => by
    obtain ⟨w, v, hw, hv, hr⟩ := h.live k hk; exact ⟨w, v, hw, (hG _).trans hv, hr⟩, h.inj⟩

theorem Post.high {C S : Nat → Bool} {ρ : Nat → Nat} {F F₁ : Std.HashMap Var LV}
    {p : Prog} {N : Nat} {γ : List Val} {n : Nat} (hf : FrameOK p N γ ρ n S F)
    (hp : Post C ρ F F₁) (hCS : ∀ k, C k = true → S k = true) {z : Nat} (hz : n ≤ z) :
    F₁[z]? = none := by
  rw [hp.2 z (fun k hk he => by have hlt : ρ k < n := hf.lt (hCS k hk); omega)]
  cases h : F[z]? with
  | none => rfl
  | some v => have := hf.fresh z v h; omega

/-- **The frame after one part**, its value then at the fresh `x`: the slots of `S` it did not
consume are still held. -/
theorem FrameOK.after {p : Prog} {N : Nat} {γ : List Val} {ρ : Nat → Nat} {n m x : Nat}
    {S C S' : Nat → Bool} {F F₁ : Std.HashMap Var LV} {va : LV}
    (hf : FrameOK p N γ ρ n S F) (hp : Post C ρ F F₁) (hCS : ∀ k, C k = true → S k = true)
    (hx : n ≤ x) (hm : x < m) (hS' : ∀ k, S' k = true → S k = true ∧ C k = false) :
    FrameOK p N γ ρ m S' (F₁.insert x va) := by
  refine ⟨fun y v hy => ?_, fun k hk => ?_, fun k k' hk hk' he =>
    hf.inj k k' (hS' k hk).1 (hS' k' hk').1 he⟩
  · rw [Std.HashMap.getElem?_insert] at hy
    by_cases hxy : x = y
    · subst hxy; exact hm
    · simp only [beq_iff_eq, hxy, if_false] at hy
      by_cases hc : ∃ k, C k = true ∧ ρ k = y
      · obtain ⟨k, hk, rfl⟩ := hc; rw [hp.1 k hk] at hy; cases hy
      · rw [hp.2 y (fun k hk he => hc ⟨k, hk, he⟩)] at hy
        exact lt_of_lt_of_le (hf.fresh y v hy) (by omega)
  · obtain ⟨hkS, hkC⟩ := hS' k hk
    obtain ⟨w, v, hw, hv, hr⟩ := hf.live k hkS
    refine ⟨w, v, hw, ?_, hr⟩
    have hne : x ≠ ρ k := by have := hf.fresh _ _ hv; omega
    rw [insert_get_ne hne, hp.2 (ρ k) (fun k' hk' he => by
      have := hf.inj k' k (hCS k' hk') hkS he
      subst this; rw [hkC] at hk'; cases hk')]
    exact hv

theorem FrameOK.erase {p : Prog} {N : Nat} {γ : List Val} {ρ : Nat → Nat} {n : Nat}
    {S : Nat → Bool} {F : Std.HashMap Var LV} (h : FrameOK p N γ ρ n S F) {x : Nat}
    (hx : ∀ k, S k = true → ρ k ≠ x) : FrameOK p N γ ρ n S (F.erase x) := by
  refine ⟨fun y v hy => ?_, fun k hk => ?_, h.inj⟩
  · by_cases hxy : x = y
    · subst hxy; rw [erase_get_self] at hy; cases hy
    · rw [erase_get_ne hxy] at hy; exact h.fresh y v hy
  · obtain ⟨w, v, hw, hv, hr⟩ := h.live k hk
    exact ⟨w, v, hw, by rw [erase_get_ne (Ne.symm (hx k hk))]; exact hv, hr⟩

/-- **A binder's value pushed** at the fresh `x`: the slot `0` holds it when `b0`. -/
theorem FrameOK.push {p : Prog} {N : Nat} {γ : List Val} {ρ : Nat → Nat} {m m' : Nat}
    {S : Nat → Bool} {F : Std.HashMap Var LV} (h : FrameOK p N γ ρ m S F) {x : Nat}
    (hxF : ∀ (y : Nat) v, F[y]? = some v → y < x) (hx : x < m') (hm : m ≤ m') {v : Val} {lv : LV}
    (hv : VRel p N v lv) (b0 : Bool) :
    FrameOK p N (v :: γ) (cons1 x ρ) m' (fun j => if j = 0 then b0 else S (j - 1))
      (F.insert x lv) := by
  refine ⟨fun y w hy => ?_, fun j hj => ?_, fun j j' hj hj' he => ?_⟩
  · by_cases hxy : x = y
    · subst hxy; exact hx
    · rw [insert_get_ne hxy] at hy; exact lt_of_lt_of_le (h.fresh y w hy) hm
  · cases j with
    | zero => exact ⟨v, lv, rfl, by simp [cons1], hv⟩
    | succ j =>
        simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at hj
        obtain ⟨w, u, hw, hu, hr⟩ := h.live j hj
        have hne : x ≠ ρ j := by have := hxF _ _ hu; omega
        refine ⟨w, u, by simpa using hw, ?_, hr⟩
        simp only [cons1, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
        rw [insert_get_ne hne]; exact hu
  · cases j with
    | zero =>
        cases j' with
        | zero => rfl
        | succ j' =>
            simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at hj'
            simp only [cons1, if_true, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at he
            obtain ⟨_, w, -, hw, -⟩ := h.live j' hj'
            have := hxF _ _ hw; omega
    | succ j =>
        cases j' with
        | zero =>
            simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at hj
            simp only [cons1, if_true, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at he
            obtain ⟨_, w, -, hw, -⟩ := h.live j hj
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

/-- **The frame after two parts**: the first consumes `Ca` from `F` to `F₁`; the second, from a
frame `G` that agrees with `F₁` below `n`, consumes the outer slots `Cb` (`hb1`, `hb2`: what it
does to the variables below `n`); the frame `F'` agrees with the second's below `n` and holds
nothing from `n` on. -/
theorem post_seq {Ca Cb C S : Nat → Bool} {ρ : Nat → Nat} {F F₁ G F₂ F' : Std.HashMap Var LV}
    {p : Prog} {N : Nat} {γ : List Val} {n : Nat} (hf : FrameOK p N γ ρ n S F)
    (hpa : Post Ca ρ F F₁) (hCa : ∀ k, Ca k = true → S k = true)
    (hG : ∀ z : Nat, z < n → G[z]? = F₁[z]?)
    (hb1 : ∀ k, Cb k = true → F₂[ρ k]? = none)
    (hb2 : ∀ x : Nat, x < n → (∀ k, Cb k = true → ρ k ≠ x) → F₂[x]? = G[x]?)
    (hCb : ∀ k, Cb k = true → S k = true) (hC : ∀ k, C k = (Ca k || Cb k))
    (hlow : ∀ z : Nat, z < n → F'[z]? = F₂[z]?) (hhigh : ∀ z : Nat, n ≤ z → F'[z]? = none) :
    Post C ρ F F' := by
  refine ⟨fun k hk => ?_, fun x hx => ?_⟩
  · rw [hC] at hk
    have hS : S k = true := by
      cases ha : Ca k
      · rw [ha, Bool.false_or] at hk; exact hCb k hk
      · exact hCa k ha
    have hρ : ρ k < n := hf.lt hS
    rw [hlow _ hρ]
    by_cases hb : Cb k = true
    · exact hb1 k hb
    · have ha : Ca k = true := by
        cases ha : Ca k
        · rw [ha, Bool.false_or] at hk; exact absurd hk hb
        · rfl
      by_cases hex : ∃ k', Cb k' = true ∧ ρ k' = ρ k
      · obtain ⟨k', hk', he⟩ := hex; rw [← he]; exact hb1 k' hk'
      · rw [hb2 _ hρ (fun k' hk' he => hex ⟨k', hk', he⟩), hG _ hρ]
        exact hpa.1 k ha
  · by_cases hxn : x < n
    · rw [hlow x hxn, hb2 x hxn (fun k hk => hx k (by rw [hC, hk, Bool.or_true])), hG x hxn]
      exact hpa.2 x (fun k hk => hx k (by rw [hC, hk, Bool.true_or]))
    · rw [hhigh x (by omega)]
      cases h : F[x]? with
      | none => rfl
      | some v => have := hf.fresh x v h; omega

/-- A part's own `Post`, read at the outer slots, for `post_seq`. -/
theorem post_parts {C : Nat → Bool} {ρ : Nat → Nat} {G F₂ : Std.HashMap Var LV} (h : Post C ρ G F₂) :
    (∀ k, C k = true → F₂[ρ k]? = none) ∧
      (∀ x : Nat, x < 0 + x + 1 → (∀ k, C k = true → ρ k ≠ x) → F₂[x]? = G[x]?) :=
  ⟨h.1, fun x _ hx => h.2 x hx⟩

/-- A binder's part's `Post`, read at the outer slots: the slots past its `d` binders, whose
variables are at or above `n`. -/
theorem post_lift {C : Nat → Bool} {ρ' ρ : Nat → Nat} {G F₂ : Std.HashMap Var LV} {d n : Nat}
    (h : Post C ρ' G F₂) (hρ : ∀ k, ρ' (k + d) = ρ k) (hlo : ∀ j, j < d → n ≤ ρ' j) :
    (∀ k, C (k + d) = true → F₂[ρ k]? = none) ∧
      (∀ x : Nat, x < n → (∀ k, C (k + d) = true → ρ k ≠ x) → F₂[x]? = G[x]?) := by
  refine ⟨fun k hk => by rw [← hρ]; exact h.1 _ hk, fun x hx hne => h.2 x (fun j hj he => ?_)⟩
  by_cases hjd : j < d
  · have := hlo j hjd; omega
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + d := ⟨j - d, by omega⟩
    rw [hρ] at he; exact hne k hj he

/-! ### The simulation of one print -/

/-- **The simulation of a print**, at derivations of size at most `sz`: a run of the source from
`e` at the values `γ` to `w`, under the LIR's allocator, is followed by the interpreter from a
frame holding the slots `e` and the rest read and a corresponding memory, to a value
corresponding to `w` and a corresponding memory, consuming the slots `e` consumes. -/
def FwdOne (p : Prog) (N sz : Nat) (ρ : Nat → Nat) (n : Nat) (out : Out) (e : Expr) (t : Tm)
    (n' : Nat) : Prop :=
  n' ≤ N → ∀ (γ : List Val) (s : St) (c : Nat) (μ : Heap) (c' : Nat) (μ' : Heap) (w : Val)
    (k : Nat), k ≤ sz → BigN (ℍ := Backend2.lirHost) bumpAlloc k c μ (Expr.psub 0 γ e) c' μ' w →
    FrameOK p N γ ρ n (need e out) s.frame → HRel p N c μ s →
    ∃ v s', VRel p N w v ∧ HRel p N c' μ' s' ∧ Post (cons e out) ρ s.frame s'.frame ∧
      ∀ rt : LTy, Sim (fun f => Backend2.eval p f rt t) s (.ok (v, s'))

/-- The interpreter's variables of a program are at `unit` below `N`. -/
def TyOK (p : Prog) (N : Nat) : Prop := ∀ x : Nat, x < N → p.ty[x]? = some LTy.unit

theorem psub_var_lt {γ : List Val} {k : Nat} {w : Val} (h : γ[k]? = some w) :
    Expr.psub 0 γ (.var k) = w.1 := by
  simp [Expr.psub, h, Val.shift_zero]

/-! #### Leaves -/

/-- A term that mentions no slot from `n` on is closed at `n`. -/
theorem closedAt_of_mentionsAt : ∀ (e : Expr) (n : Nat), (∀ k, n ≤ k → mentions e k = false) →
    BoCa.Fig16.LogRel.Core.closedAt n e = true
  | .var i, n, h => by
      simp only [BoCa.Fig16.LogRel.Core.closedAt, decide_eq_true_eq]
      by_contra hc
      have := h i (by omega); simp [mentions] at this
  | .unit, _, _ | .loc _, _, _ | .prim _, _, _ => rfl
  | .pair a b, n, h | .seq a b, n, h | .app a b, n, h => by
      simp only [BoCa.Fig16.LogRel.Core.closedAt, Bool.and_eq_true]
      exact ⟨closedAt_of_mentionsAt a n (fun k hk => by have := h k hk; simp_all [mentions]),
        closedAt_of_mentionsAt b n (fun k hk => by have := h k hk; simp_all [mentions])⟩
  | .inj₁ a, n, h | .inj₂ a, n, h => closedAt_of_mentionsAt a n (fun k hk => h k hk)
  | .lam b, n, h => closedAt_of_mentionsAt b (n + 1) (fun k hk => by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact h j (by omega))
  | .letpair a b, n, h => by
      simp only [BoCa.Fig16.LogRel.Core.closedAt, Bool.and_eq_true]
      refine ⟨closedAt_of_mentionsAt a n (fun k hk => by have := h k hk; simp_all [mentions]),
        closedAt_of_mentionsAt b (n + 2) (fun k hk => ?_)⟩
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      have := h j (by omega); simp_all [mentions]
  | .case v a b, n, h => by
      simp only [BoCa.Fig16.LogRel.Core.closedAt, Bool.and_eq_true]
      refine ⟨⟨closedAt_of_mentionsAt v n (fun k hk => by have := h k hk; simp_all [mentions]),
        closedAt_of_mentionsAt a (n + 1) (fun k hk => ?_)⟩,
        closedAt_of_mentionsAt b (n + 1) (fun k hk => ?_)⟩
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have := h j (by omega); simp_all [mentions]
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have := h j (by omega); simp_all [mentions]

theorem closedAt_of_mentions {e : Expr} (h : ∀ k, mentions e k = false) :
    BoCa.Fig16.LogRel.Core.closedAt 0 e = true :=
  closedAt_of_mentionsAt e 0 (fun k _ => h k)

theorem post_none {C : Nat → Bool} {ρ : Nat → Nat} {F : Std.HashMap Var LV}
    (h : ∀ k, C k = false) : Post C ρ F F :=
  ⟨fun k hk => absurd hk (by rw [h k]; simp), fun _ _ => rfl⟩

theorem fwd_value {p : Prog} {N sz : Nat} {ρ : Nat → Nat} {n : Nat} {out : Out} {e : Expr}
    {t : Tm} (v : Val) (lv : LV) (he : e = v.1) (hcl : ∀ k, mentions e k = false)
    (hrel : VRel p N v lv)
    (hsim : ∀ (s : St) (rt : LTy), Sim (fun f => Backend2.eval p f rt t) s (.ok (lv, s))) :
    FwdOne p N sz ρ n out e t n := by
  intro _ γ s c μ c' μ' w kk _ hb _ hh
  have hpe : Expr.psub 0 γ e = v.1 := by
    subst he
    exact BoCa.Fig16.LogRel.Core.psub_closedAt _ γ (closedAt_of_mentions hcl) (Nat.zero_le 0)
  rw [hpe] at hb
  obtain ⟨rfl, rfl, rfl⟩ := big_val_inv hb v rfl
  exact ⟨lv, s, hrel, hh, post_none (fun k => by simp [cons, hcl k]), hsim s⟩

theorem sim_clos_nil {p : Prog} {rt : LTy} {c : Nat} {s : St} :
    Sim (fun f => Backend2.eval p f rt (.clos c [])) s (.ok (.clos c [], s)) := by
  have h := sim_clos (p := p) (rt := rt) (c := c) (env := []) (vs := []) (s := s) rfl
  simpa [eraseL] using h

theorem sim_locAt {p : Prog} {rt : LTy} {ℓ : Nat} {s : St} :
    Sim (fun f => Backend2.eval p f rt (.prim (.locAt ℓ) [])) s (.ok (.loc ℓ, s)) :=
  sim_prim (fun f => by rw [Backend2.eval] <;> simp) rfl

theorem fwd_varMove {p : Prog} {N sz : Nat} (ρ : Nat → Nat) (n : Nat) (out : Out) (k : Nat)
    (h : out k = false) : FwdOne p N sz ρ n out (.var k) (.var (ρ k)) n := by
  intro _ γ s c μ c' μ' w kk _ hb hf hh
  obtain ⟨w', v, hw', hv, hr⟩ := hf.live k (by simp [need, mentions])
  rw [psub_var_lt hw'] at hb
  obtain ⟨rfl, rfl, rfl⟩ := big_val_inv hb w' rfl
  refine ⟨v, { s with frame := s.frame.erase (ρ k) }, hr, hh.frame _, ⟨fun j hj => ?_, fun x hx => ?_⟩,
    fun rt => sim_var hv⟩
  · have : j = k := (by simpa [cons, mentions] using hj : k = j ∧ _).1.symm
    subst this; exact erase_get_self
  · exact erase_get_ne (hx k (by simp [cons, mentions, h]))

theorem fwd_varCopy {p : Prog} {N sz : Nat} (hty : TyOK p N) (ρ : Nat → Nat) (n : Nat)
    (out : Out) (k : Nat) (h : out k = true) :
    FwdOne p N sz ρ n out (.var k) (.copy (ρ k) n (.var n)) (n + 1) := by
  intro hN γ s c μ c' μ' w kk _ hb hf hh
  have hk : need (.var k) out k = true := by simp [need, h]
  obtain ⟨w', v, hw', hv, hr⟩ := hf.live k hk
  rw [psub_var_lt hw'] at hb
  obtain ⟨rfl, rfl, rfl⟩ := big_val_inv hb w' rfl
  have hn : s.frame[n]? = none := by
    cases h' : s.frame[n]? with
    | none => rfl
    | some u => have := hf.fresh n u h'; omega
  have hcons : ∀ j, cons (.var k) out j = false := fun j => by
    by_cases hj : k = j
    · subst hj; simp [cons, h]
    · simp [cons, mentions, hj]
  refine ⟨v, { s with frame := (s.frame.insert n v).erase n }, hr, hh.frame _,
    ⟨fun j hj => absurd hj (by rw [hcons j]; simp), fun x _ => ?_⟩, ?_⟩
  · show ((s.frame.insert n v).erase n)[x]? = s.frame[x]?
    by_cases hx : n = x
    · subst hx; rw [erase_get_self, hn]
    · rw [erase_get_ne hx, insert_get_ne hx]
  · intro rt
    have hρ := hf.lt hk
    exact sim_copy (hty _ (by omega)) hv (sim_var (s := { s with frame := s.frame.insert n v })
      insert_get_self)

/-! #### Two parts in order -/

/-- The fresh variables a part leaves behind: none at or above `n`. -/
theorem fresh_none {p : Prog} {N : Nat} {γ : List Val} {ρ : Nat → Nat} {n : Nat}
    {S : Nat → Bool} {F : Std.HashMap Var LV} (hf : FrameOK p N γ ρ n S F) {z : Nat}
    (hz : n ≤ z) : F[z]? = none := by
  cases h : F[z]? with
  | none => rfl
  | some v => have := hf.fresh z v h; omega

/-- **Two parts in order**, the first's value at the fresh `n`, the second's at `n + 1`: what
`post_seq` needs of the frames the second part and the operation after leave. -/
theorem post_seq2 {Ca Cb C S : Nat → Bool} {ρ : Nat → Nat} {F F₁ F₂ : Std.HashMap Var LV}
    {p : Prog} {N : Nat} {γ : List Val} {n : Nat} {va vb : LV} (hf : FrameOK p N γ ρ n S F)
    (hpa : Post Ca ρ F F₁) (hCa : ∀ k, Ca k = true → S k = true)
    (hpb : Post Cb ρ (F₁.insert n va) F₂) (hCb : ∀ k, Cb k = true → S k = true)
    (hC : ∀ k, C k = (Ca k || Cb k)) :
    F₂[n]? = some va ∧ Post C ρ F (((F₂.insert (n + 1) vb).erase n).erase (n + 1)) := by
  have hn : F₂[n]? = some va := by
    rw [hpb.2 n (fun k hk he => by have := hf.lt (hCb k hk); omega)]; exact insert_get_self
  refine ⟨hn, post_seq hf hpa hCa (G := F₁.insert n va) (fun z hz => insert_get_ne (by omega))
    hpb.1 (fun x _ hx => hpb.2 x hx) hCb hC (fun z hz => ?_) (fun z hz => ?_)⟩
  · rw [erase_get_ne (by omega), erase_get_ne (by omega), insert_get_ne (by omega)]
  · by_cases h1 : n + 1 = z
    · subst h1; exact erase_get_self
    rw [erase_get_ne h1]
    by_cases h2 : n = z
    · subst h2; exact erase_get_self
    rw [erase_get_ne h2, insert_get_ne h1, hpb.2 z (fun k hk he => by
      have := hf.lt (hCb k hk); omega), insert_get_ne h2]
    exact hpa.high hf hCa hz

/-- One part, its value at the fresh `n`, then an operation that consumes it. -/
theorem post_one {Ca C S : Nat → Bool} {ρ : Nat → Nat} {F F₁ : Std.HashMap Var LV}
    {p : Prog} {N : Nat} {γ : List Val} {n : Nat} {va : LV} (hf : FrameOK p N γ ρ n S F)
    (hpa : Post Ca ρ F F₁) (hCa : ∀ k, Ca k = true → S k = true) (hC : ∀ k, C k = Ca k) :
    Post C ρ F ((F₁.insert n va).erase n) := by
  refine ⟨fun k hk => ?_, fun x hx => ?_⟩
  · rw [hC] at hk
    have := hf.lt (hCa k hk)
    rw [erase_get_ne (by omega), insert_get_ne (by omega)]; exact hpa.1 k hk
  · by_cases hxn : n = x
    · subst hxn; rw [erase_get_self, fresh_none hf (le_refl _)]
    · rw [erase_get_ne hxn, insert_get_ne hxn]; exact hpa.2 x (fun k hk => hx k (by rw [hC]; exact hk))

theorem fwd_pair {p : Prog} {N sz : Nat} {ρ : Nat → Nat} {n n₁ n₂ : Nat} {out : Out} {a b : Expr}
    {ta tb : Tm} (hty : TyOK p N)
    (ha : Pr p N ρ (n + 2) (unionO out (fvAt 0 b)) a ta n₁) (hb : Pr p N ρ n₁ out b tb n₂)
    (iha : FwdOne p N sz ρ (n + 2) (unionO out (fvAt 0 b)) a ta n₁)
    (ihb : FwdOne p N sz ρ n₁ out b tb n₂) :
    FwdOne p N sz ρ n out (.pair a b) (.letv n ta (.letv (n + 1) tb (.pair n (n + 1)))) n₂ := by
  intro hN γ s c μ c' μ' w kk hk hbig hf hh
  have hn₁ := pr_le ha; have hn₂ := pr_le hb
  simp only [Expr.psub] at hbig
  obtain ⟨i, j, c₁, μ₁, u₁, u₂, hi, hj, hba, hbb, rfl⟩ := big_pair_inv hbig
  obtain ⟨va, s₁, hva, hh₁, hpa, hsa⟩ := iha (by omega) γ s c μ c₁ μ₁ u₁ i (by omega) hba
    (hf.mono (by omega) (fun k hk => by
      simp only [need, unionO, fvAt, mentions, Nat.add_zero, Bool.or_eq_true] at hk ⊢; tauto))
    hh
  have hCa : ∀ k, cons a (unionO out (fvAt 0 b)) k = true → need (.pair a b) out k = true := by
    intro k hk
    simp only [cons, need, unionO, fvAt, mentions, Nat.add_zero, Bool.or_eq_true, Bool.and_eq_true,
      Bool.not_eq_true'] at hk ⊢; tauto
  have hfb : FrameOK p N γ ρ n₁ (need b out) (s₁.frame.insert n va) :=
    hf.after hpa hCa (le_refl n) (by omega) (fun k hk => by
      simp only [cons, need, unionO, fvAt, mentions, Nat.add_zero, Bool.or_eq_true,
        Bool.and_eq_false_iff, Bool.not_eq_false'] at hk ⊢
      exact ⟨by tauto, by tauto⟩)
  obtain ⟨vb, s₂, hvb, hh₂, hpb, hsb⟩ := ihb (by omega) γ { s₁ with frame := s₁.frame.insert n va }
    c₁ μ₁ c' μ' u₂ j (by omega) hbb hfb (hh₁.frame _)
  obtain ⟨hn, hpost⟩ := post_seq2 (C := cons (.pair a b) out) (vb := vb) hf hpa hCa hpb (fun k hk => by
      simp only [cons, need, mentions, Bool.or_eq_true, Bool.and_eq_true] at hk ⊢; tauto)
    (fun k => by
      simp only [cons, unionO, fvAt, mentions, Nat.add_zero]
      cases mentions a k <;> cases mentions b k <;> cases out k <;> rfl)
  refine ⟨.pair va vb, { s₂ with frame := ((s₂.frame.insert (n + 1) vb).erase n).erase (n + 1) },
    .pair hva hvb, hh₂.frame _, hpost, fun rt => ?_⟩
  refine sim_letv (hty n (by omega)) (hsa LTy.unit) (sim_letv (hty (n + 1) (by omega)) (hsb LTy.unit) ?_)
  exact sim_pair (s := { s₂ with frame := s₂.frame.insert (n + 1) vb })
    (by show (s₂.frame.insert (n + 1) vb)[n]? = _; rw [insert_get_ne (by omega)]; exact hn)
    (by show ((s₂.frame.insert (n + 1) vb).erase n)[n + 1]? = _
        rw [erase_get_ne (by omega)]; exact insert_get_self)

theorem fwd_inj {p : Prog} {N sz : Nat} {ρ : Nat → Nat} {n n₁ : Nat} {out : Out} {a : Expr}
    {ta : Tm} (r : Bool) (hty : TyOK p N)
    (ha : Pr p N ρ (n + 1) out a ta n₁) (iha : FwdOne p N sz ρ (n + 1) out a ta n₁) :
    FwdOne p N sz ρ n out (if r then .inj₂ a else .inj₁ a) (.letv n ta (.inj r n)) n₁ := by
  intro hN γ s c μ c' μ' w kk hk hbig hf hh
  have hn₁ := pr_le ha
  have hm : ∀ k, mentions (if r then .inj₂ a else .inj₁ a) k = mentions a k := by
    intro k; cases r <;> rfl
  have key : ∃ i u, i ≤ kk ∧ BigN (ℍ := Backend2.lirHost) bumpAlloc i c μ (Expr.psub 0 γ a) c' μ' u ∧
      w = (if r then Val.inj₂ u else Val.inj₁ u) := by
    cases r
    · obtain ⟨i, u, hi, h, rfl⟩ := big_inj₁_inv (by simpa [Expr.psub] using hbig)
      exact ⟨i, u, hi, h, rfl⟩
    · obtain ⟨i, u, hi, h, rfl⟩ := big_inj₂_inv (by simpa [Expr.psub] using hbig)
      exact ⟨i, u, hi, h, rfl⟩
  obtain ⟨i, u, hi, hba, rfl⟩ := key
  obtain ⟨va, s₁, hva, hh₁, hpa, hsa⟩ := iha (by omega) γ s c μ c' μ' u i (by omega) hba
    (hf.mono (by omega) (fun k hk => by simpa [need, hm] using hk)) hh
  refine ⟨.inj r va, { s₁ with frame := (s₁.frame.insert n va).erase n }, ?_, hh₁.frame _,
    post_one hf hpa (fun k hk => by simp_all [cons, need]) (fun k => by simp [cons, hm]),
    fun rt => sim_letv (hty n (by omega)) (hsa LTy.unit) (sim_inj (s := { s₁ with frame := s₁.frame.insert n va })
      insert_get_self)⟩
  cases r
  · exact .inj₁ hva
  · exact .inj₂ hva

theorem vrel_unit_inv {p : Prog} {N : Nat} {lv : LV} (h : VRel p N Val.unit lv) : lv = .unit := by
  generalize hV : Val.unit = V at h
  cases h with
  | unit => rfl
  | _ => have e := congrArg Subtype.val hV; simp [Val.pair, Val.unit, Val.prim, Val.inj₁,
      Val.inj₂, Val.lam, Val.loc, Val.storeV] at e

theorem fwd_seq {p : Prog} {N sz : Nat} {ρ : Nat → Nat} {n n₁ n₂ : Nat} {out : Out} {a b : Expr}
    {ta tb : Tm} (hty : TyOK p N)
    (ha : Pr p N ρ (n + 1) (unionO out (fvAt 0 b)) a ta n₁) (hb : Pr p N ρ n₁ out b tb n₂)
    (iha : FwdOne p N sz ρ (n + 1) (unionO out (fvAt 0 b)) a ta n₁)
    (ihb : FwdOne p N sz ρ n₁ out b tb n₂) :
    FwdOne p N sz ρ n out (.seq a b) (.letv n ta (.drop n tb)) n₂ := by
  intro hN γ s c μ c' μ' w kk hk hbig hf hh
  have hn₁ := pr_le ha; have hn₂ := pr_le hb
  simp only [Expr.psub] at hbig
  obtain ⟨i, j, c₁, μ₁, hi, hj, hba, hbb⟩ := big_seq_inv hbig
  obtain ⟨va, s₁, hva, hh₁, hpa, hsa⟩ := iha (by omega) γ s c μ c₁ μ₁ Val.unit i (by omega) hba
    (hf.mono (by omega) (fun k hk => by
      simp only [need, unionO, fvAt, mentions, Nat.add_zero, Bool.or_eq_true] at hk ⊢; tauto))
    hh
  obtain rfl := vrel_unit_inv hva
  have hCa : ∀ k, cons a (unionO out (fvAt 0 b)) k = true → need (.seq a b) out k = true := by
    intro k hk
    simp only [cons, need, unionO, fvAt, mentions, Nat.add_zero, Bool.or_eq_true, Bool.and_eq_true,
      Bool.not_eq_true'] at hk ⊢; tauto
  have hfb : FrameOK p N γ ρ n₁ (need b out) ((s₁.frame.insert n LV.unit).erase n) :=
    (hf.after hpa hCa (le_refl n) (by omega) (fun k hk => by
      simp only [cons, need, unionO, fvAt, mentions, Nat.add_zero, Bool.or_eq_true,
        Bool.and_eq_false_iff, Bool.not_eq_false'] at hk ⊢
      exact ⟨by tauto, by tauto⟩)).erase (fun k hk he => by
        have := hf.lt (S := need (.seq a b) out) (k := k) (by
          simp only [need, mentions, Bool.or_eq_true] at hk ⊢; tauto)
        omega)
  obtain ⟨vb, s₂, hvb, hh₂, hpb, hsb⟩ := ihb (by omega) γ
    { s₁ with frame := (s₁.frame.insert n LV.unit).erase n } c₁ μ₁ c' μ' w j (by omega) hbb hfb
    (hh₁.frame _)
  have hCb : ∀ k, cons b out k = true → need (.seq a b) out k = true := fun k hk => by
    simp only [cons, need, mentions, Bool.or_eq_true, Bool.and_eq_true] at hk ⊢; tauto
  refine ⟨vb, s₂, hvb, hh₂, post_seq (C := cons (.seq a b) out) hf hpa hCa
    (G := (s₁.frame.insert n LV.unit).erase n)
    (fun z hz => by rw [erase_get_ne (by omega), insert_get_ne (by omega)])
    hpb.1 (fun x _ hx => hpb.2 x hx) hCb
    (fun k => by
      simp only [cons, unionO, fvAt, mentions, Nat.add_zero]
      cases mentions a k <;> cases mentions b k <;> cases out k <;> rfl)
    (fun z _ => rfl) (fun z hz => ?_), fun rt => ?_⟩
  · rw [hpb.2 z (fun k hk he => by have := hf.lt (hCb k hk); omega)]
    show ((s₁.frame.insert n LV.unit).erase n)[z]? = none
    by_cases hzn : n = z
    · subst hzn; exact erase_get_self
    · rw [erase_get_ne hzn, insert_get_ne hzn]; exact hpa.high hf hCa hz
  · exact sim_letv (hty n (by omega)) (hsa LTy.unit) (sim_drop (hty n (by omega)) insert_get_self (hsb rt))

/-! #### Binders -/

theorem liftO_add (d : Nat) (o : Out) (k : Nat) : liftO d o (k + d) = o k := by
  simp [liftO]

theorem liftO_lt {d : Nat} (o : Out) {k : Nat} (h : k < d) : liftO d o k = false := by
  simp [liftO]; omega

theorem FrameOK.eraseIf {p : Prog} {N : Nat} {γ : List Val} {ρ : Nat → Nat} {n : Nat}
    {S : Nat → Bool} {F : Std.HashMap Var LV} (h : FrameOK p N γ ρ n S F) (c : Bool) {x : Nat}
    (hx : c = true → ∀ k, S k = true → ρ k ≠ x) :
    FrameOK p N γ ρ n S (if c = true then F.erase x else F) := by
  cases c
  · exact h
  · exact h.erase (hx rfl)

theorem sim_dropIf {p : Prog} {rt : LTy} {c : Bool} {x : Var} {t : Tm} {s : St}
    {r : Except String (LV × St)} (hty : p.ty[x]? = some .unit)
    (hx : c = true → ∃ v, s.frame[x]? = some v)
    (ht : Sim (fun f => Backend2.eval p f rt t)
      ({ s with frame := if c then s.frame.erase x else s.frame } : St) r) :
    Sim (fun f => Backend2.eval p f rt (dropIf c x t)) s r := by
  cases c
  · exact ht
  · obtain ⟨v, hv⟩ := hx rfl
    exact sim_drop hty hv ht

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
      Val.inj₂, Val.lam, Val.loc, Val.storeV] at e

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
      Val.inj₂, Val.lam, Val.loc, Val.storeV] at e

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
      Val.inj₂, Val.lam, Val.loc, Val.storeV] at e

theorem psub_arm (γ : List Val) (v : Val) (a : Expr) :
    (Expr.psub 1 γ a).subst 0 v = Expr.psub 0 (v :: γ) a := by
  rw [Expr.psub_cons 0 v γ a, Val.shift_zero]

theorem psub_body2 (γ : List Val) (v₁ v₂ : Val) (b : Expr) :
    ((Expr.psub 2 γ b).subst 0 (v₂.shift 1 0)).subst 0 v₁ = Expr.psub 0 (v₂ :: v₁ :: γ) b := by
  rw [Expr.psub_cons₂ 0 v₂ v₁ γ b, Val.shift_zero]

/-- What a part that ran from `G` leaves at or above `n`: nothing, when every variable `G` holds
there is one of a slot the part consumes. -/
theorem high_none {C : Nat → Bool} {ρ' : Nat → Nat} {G F₂ : Std.HashMap Var LV} {n : Nat}
    (hpb : Post C ρ' G F₂) (hG : ∀ z : Nat, n ≤ z → G[z]? ≠ none → ∃ k, C k = true ∧ ρ' k = z)
    {z : Nat} (hz : n ≤ z) : F₂[z]? = none := by
  by_cases hex : ∃ k, C k = true ∧ ρ' k = z
  · obtain ⟨k, hk, rfl⟩ := hex; exact hpb.1 k hk
  · rw [hpb.2 z (fun k hk he => hex ⟨k, hk, he⟩)]
    by_contra hne
    exact hex (hG z hz hne)

theorem fwd_letpair {p : Prog} {N sz : Nat} {ρ : Nat → Nat} {n n₁ n₂ : Nat} {out : Out}
    {a b : Expr} {ta tb : Tm} (hty : TyOK p N)
    (ha : Pr p N ρ (n + 3) (unionO out (fvAt 2 b)) a ta n₁)
    (hb : Pr p N (cons2 (n + 2) (n + 1) ρ) n₁ (liftO 2 out) b tb n₂)
    (iha : FwdOne p N sz ρ (n + 3) (unionO out (fvAt 2 b)) a ta n₁)
    (ihb : FwdOne p N sz (cons2 (n + 2) (n + 1) ρ) n₁ (liftO 2 out) b tb n₂) :
    FwdOne p N sz ρ n out (.letpair a b) (.letv n ta (.letpair (n + 1) (n + 2) n
      (dropIf (!mentions b 1) (n + 1) (dropIf (!mentions b 0) (n + 2) tb)))) n₂ := by
  intro hN γ s c μ c' μ' w kk hk hbig hf hh
  have hn₁ := pr_le ha; have hn₂ := pr_le hb
  simp only [Expr.psub] at hbig
  obtain ⟨i, j, c₁, μ₁, v₁, v₂, hi, hj, hba, hbb⟩ := big_letpair_inv hbig
  rw [psub_body2] at hbb
  obtain ⟨va, s₁, hva, hh₁, hpa, hsa⟩ := iha (by omega) γ s c μ c₁ μ₁ _ i (by omega) hba
    (hf.mono (by omega) (fun k hk => by
      simp only [need, unionO, fvAt, mentions, Bool.or_eq_true] at hk ⊢; tauto))
    hh
  obtain ⟨lx, ly, rfl, hx₁, hx₂⟩ := vrel_pair_inv hva
  have hCa : ∀ k, cons a (unionO out (fvAt 2 b)) k = true → need (.letpair a b) out k = true := by
    intro k hk
    simp only [cons, need, unionO, fvAt, mentions, Bool.or_eq_true, Bool.and_eq_true,
      Bool.not_eq_true'] at hk ⊢; tauto
  let S₀ : Nat → Bool := fun k => need b (liftO 2 out) (k + 2)
  have hF₀ : FrameOK p N γ ρ (n + 1) S₀ ((s₁.frame.insert n (.pair lx ly)).erase n) :=
    (hf.after hpa hCa (le_refl n) (by omega) (fun k hk => by
      simp only [S₀, cons, need, unionO, fvAt, liftO_add, mentions] at hk ⊢
      revert hk
      cases mentions a k <;> cases mentions b (k + 2) <;> cases out k <;> decide)).erase
      (fun k hk he => by
        have := hf.lt (S := need (.letpair a b) out) (k := k) (by
          simp only [S₀, need, liftO_add, mentions] at hk ⊢
          revert hk
          cases mentions a k <;> cases mentions b (k + 2) <;> cases out k <;> decide)
        omega)
  have hkeys : ∀ (z : Nat) u, ((s₁.frame.insert n (.pair lx ly)).erase n)[z]? = some u → z < n := by
    intro z u hz
    by_cases hzn : n = z
    · subst hzn; rw [erase_get_self] at hz; cases hz
    · rw [erase_get_ne hzn, insert_get_ne hzn] at hz
      by_contra hc
      rw [hpa.high hf hCa (by omega)] at hz; cases hz
  have hF₁ := hF₀.push (fun z u hz => Nat.lt_succ_of_lt (hkeys z u hz)) (x := n + 1) (by omega)
    (by omega) hx₁ (mentions b 1) (m' := n + 2)
  have hF₂ := hF₁.push (x := n + 2) (fun z u hz => by
      by_cases hzx : n + 1 = z
      · omega
      · rw [insert_get_ne hzx] at hz; have := hkeys z u hz; omega) (by omega) (by omega) hx₂
      (mentions b 0) (m' := n₁)
  rw [← cons2_eq] at hF₂
  -- the frame the body starts from, its unread binders dropped
  let G₀ := (((s₁.frame.insert n (.pair lx ly)).erase n).insert (n + 1) lx).insert (n + 2) ly
  let G₁ := if (!mentions b 1) = true then G₀.erase (n + 1) else G₀
  let G := if (!mentions b 0) = true then G₁.erase (n + 2) else G₁
  have hSb : ∀ k, need b (liftO 2 out) k = true →
      (fun j => if j = 0 then mentions b 0 else
        (fun j => if j = 0 then mentions b 1 else S₀ (j - 1)) (j - 1)) k = true := by
    intro k hk
    rcases k with _ | _ | k
    · simpa [need, liftO] using hk
    · simpa [need, liftO] using hk
    · simpa [S₀] using hk
  have hfb : FrameOK p N (v₂ :: v₁ :: γ) (cons2 (n + 2) (n + 1) ρ) n₁ (need b (liftO 2 out)) G := by
    refine FrameOK.mono ?_ (le_refl _) hSb
    refine (hF₂.eraseIf _ (fun h1 k hk he => ?_)).eraseIf _ (fun h0 k hk he => ?_)
    · rcases k with _ | _ | k
      · simp [cons2] at he
      · simp only [Bool.not_eq_true'] at h1; simp [h1] at hk
      · simp [cons2] at he; have := hF₀.lt (by simpa using hk); omega
    · rcases k with _ | _ | k
      · simp only [Bool.not_eq_true'] at h0; simp [h0] at hk
      · simp [cons2] at he
      · simp [cons2] at he; have := hF₀.lt (by simpa using hk); omega
  obtain ⟨vw, s₂, hvw, hh₂, hpb, hsb⟩ := ihb (by omega) (v₂ :: v₁ :: γ) { s₁ with frame := G }
    c₁ μ₁ c' μ' w j (by omega) hbb hfb (hh₁.frame _)
  have hρ2 : ∀ k, cons2 (n + 2) (n + 1) ρ (k + 2) = ρ k := fun k => by simp [cons2]
  obtain ⟨hb1, hb2⟩ := post_lift (d := 2) (n := n) hpb hρ2 (fun jj hjj => by
    rcases jj with _ | _ | jj
    · simp [cons2]
    · simp [cons2]
    · omega)
  have hCb : ∀ k, cons b (liftO 2 out) (k + 2) = true → need (.letpair a b) out k = true := by
    intro k hk
    simp only [cons, need, liftO, mentions, Bool.or_eq_true, Bool.and_eq_true] at hk ⊢; tauto
  have hGlow : ∀ z : Nat, z < n → G[z]? = s₁.frame[z]? := by
    intro z hz
    simp only [G, G₁, G₀]
    split <;> split <;>
      simp only [erase_get_ne (show n + 2 ≠ z by omega), erase_get_ne (show n + 1 ≠ z by omega),
        insert_get_ne (show n + 2 ≠ z by omega), insert_get_ne (show n + 1 ≠ z by omega),
        erase_get_ne (show n ≠ z by omega), insert_get_ne (show n ≠ z by omega)]
  refine ⟨vw, s₂, hvw, hh₂, post_seq (C := cons (.letpair a b) out) hf hpa hCa (G := G) hGlow
    hb1 hb2 hCb (fun k => by
      simp only [cons, unionO, fvAt, liftO, mentions]
      simp only [Nat.add_sub_cancel, show 2 ≤ k + 2 from by omega, decide_true, Bool.true_and]
      cases mentions a k <;> cases mentions b (k + 2) <;> cases out k <;> rfl)
    (fun z _ => rfl) (fun z hz => ?_), fun rt => ?_⟩
  · refine high_none hpb (fun z' hz' hne => ?_) hz
    have hG₀ : ∀ z'' : Nat, n ≤ z'' → z'' ≠ n + 1 → z'' ≠ n + 2 → G₀[z'']? = none := by
      intro z'' h1 h2 h3
      simp only [G₀]
      rw [insert_get_ne (Ne.symm h3), insert_get_ne (Ne.symm h2)]
      by_cases hzn : n = z''
      · subst hzn; exact erase_get_self
      · rw [erase_get_ne hzn, insert_get_ne hzn]; exact hpa.high hf hCa (by omega)
    by_cases h2 : z' = n + 2
    · subst h2
      refine ⟨0, ?_, by simp [cons2]⟩
      cases h0 : mentions b 0
      · exfalso; apply hne; simp [G, h0]
      · simp [cons, h0, liftO_lt out (show 0 < 2 by omega)]
    by_cases h1 : z' = n + 1
    · subst h1
      refine ⟨1, ?_, by simp [cons2]⟩
      cases h1' : mentions b 1
      · exfalso; apply hne
        simp only [G, G₁, h1', Bool.not_false, if_true]
        split <;> simp
      · simp [cons, h1', liftO_lt out (show 1 < 2 by omega)]
    · exfalso; apply hne
      simp only [G, G₁]
      split <;> split <;>
        (try simp only [erase_get_ne (show n + 2 ≠ z' by omega),
          erase_get_ne (show n + 1 ≠ z' by omega)]) <;>
        exact hG₀ z' hz' h1 h2
  · have hq : (s₁.frame.insert n (.pair lx ly))[n]? = some (.pair lx ly) := insert_get_self
    refine sim_letv (hty n (by omega)) (hsa LTy.unit) (sim_letpair hq ?_)
    refine sim_dropIf (hty _ (by omega)) (fun _ => ⟨lx, ?_⟩) ?_
    · show G₀[n + 1]? = some lx
      simp only [G₀]; rw [insert_get_ne (by omega)]; exact insert_get_self
    refine sim_dropIf (hty _ (by omega)) (fun _ => ⟨ly, ?_⟩) (hsb rt)
    show G₁[n + 2]? = some ly
    simp only [G₁, G₀]
    split
    · rw [erase_get_ne (by omega)]; exact insert_get_self
    · exact insert_get_self

/-! #### Cases -/

theorem FrameOK.eraseL {p : Prog} {N : Nat} {γ : List Val} {ρ : Nat → Nat} {n : Nat}
    {S : Nat → Bool} : ∀ (xs : List Var) {F : Std.HashMap Var LV}, FrameOK p N γ ρ n S F →
    (∀ x ∈ xs, ∀ k, S k = true → ρ k ≠ x) → FrameOK p N γ ρ n S (eraseL F xs)
  | [], _, h, _ => h
  | x :: xs, _, h, hx => FrameOK.eraseL xs (h.erase (hx x (by simp)))
      (fun y hy => hx y (by simp [hy]))

theorem sim_dropsT {p : Prog} {N : Nat} (hty : TyOK p N) {rt : LTy} {t : Tm}
    {r : Except String (LV × St)} : ∀ (xs : List Nat) (s : St), xs.Nodup →
    (∀ x : Nat, x ∈ xs → x < N ∧ ∃ v, s.frame[x]? = some v) →
    Sim (fun f => Backend2.eval p f rt t) ({ s with frame := eraseL s.frame xs } : St) r →
    Sim (fun f => Backend2.eval p f rt (dropsT xs t)) s r
  | [], s, _, _, h => h
  | x :: xs, s, hn, hx, h => by
      obtain ⟨hxN, v, hv⟩ := hx x (by simp)
      have hn' := List.nodup_cons.mp hn
      refine sim_drop (hty x hxN) hv (sim_dropsT hty xs _ hn'.2 (fun y hy => ?_) h)
      obtain ⟨hyN, u, hu⟩ := hx y (by simp [hy])
      refine ⟨hyN, u, ?_⟩
      show (s.frame.erase x)[y]? = some u
      rw [erase_get_ne (fun (he : x = y) => hn'.1 (he ▸ hy))]; exact hu

theorem armDrops_mem {out : Out} {a b : Expr} {k : Nat} :
    k ∈ armDrops out a b ↔ (mentions b (k + 1) && !mentions a (k + 1) && !out k) = true := by
  simp only [armDrops, slotsOf, List.mem_filter, List.mem_range, and_iff_right_iff_imp]
  intro h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  have := mentions_lt h.1.1; omega

theorem armDrops_nodup (out : Out) (a b : Expr) : (armDrops out a b).Nodup :=
  List.nodup_range.filter _

/-- **An arm of a `case`**: the injection's payload at the fresh `x`, the slots only the other
arm reads dropped, then the arm. -/
theorem fwd_arm {p : Prog} {N sz : Nat} {ρ : Nat → Nat} {n x m m' : Nat} {out : Out}
    {sv a b : Expr} {ta : Tm} (hty : TyOK p N) (hnx : n < x) (hxm : x < m) (hmm : m ≤ m')
    (hN : m' ≤ N) (iha : FwdOne p N sz (cons1 x ρ) m (liftO 1 out) a ta m')
    {S Cs C : Nat → Bool} {γ : List Val} {F : Std.HashMap Var LV} {s₁ : St} {lv₀ : LV}
    (hS : ∀ k, S k = (mentions sv k || mentions a (k + 1) || mentions b (k + 1) || out k))
    (hCsd : ∀ k, Cs k = (mentions sv k && !(out k || mentions a (k + 1) || mentions b (k + 1))))
    (hC : ∀ k, C k = ((mentions sv k || mentions a (k + 1) || mentions b (k + 1)) && !out k))
    (hf : FrameOK p N γ ρ n S F) (hpa : Post Cs ρ F s₁.frame)
    {u : Val} {lu : LV} (hlu : VRel p N u lu) {c₁ c' : Nat} {μ₁ μ' : Heap} {w : Val} {j : Nat}
    (hj : j ≤ sz)
    (hba : BigN (ℍ := Backend2.lirHost) bumpAlloc j c₁ μ₁ (Expr.psub 0 (u :: γ) a) c' μ' w)
    (hh₁ : HRel p N c₁ μ₁ s₁) :
    ∃ v s', VRel p N w v ∧ HRel p N c' μ' s' ∧ Post C ρ F s'.frame ∧
      ∀ rt : LTy, Sim (fun f => Backend2.eval p f rt
          (dropIf (!mentions a 0) x (dropsT ((armDrops out a b).map ρ) ta)))
        ({ s₁ with frame := ((s₁.frame.insert n lv₀).erase n).insert x lu } : St) (.ok (v, s')) := by
  have hCsS : ∀ k, Cs k = true → S k = true := fun k hk => by
    rw [hCsd] at hk; rw [hS]
    simp only [Bool.and_eq_true] at hk; simp [hk.1]
  let S' : Nat → Bool := fun k => out k || mentions a (k + 1) || mentions b (k + 1)
  have hS'S : ∀ k, S' k = true → S k = true := fun k hk => by
    rw [hS]; simp only [S', Bool.or_eq_true] at hk ⊢; tauto
  let B := (s₁.frame.insert n lv₀).erase n
  have hB : FrameOK p N γ ρ (n + 1) S' B :=
    (hf.after (m := n + 1) hpa hCsS (le_refl n) (by omega) (fun k hk => ⟨hS'S k hk, by
      rw [hCsd]; simp only [S'] at hk; simp [hk]⟩)).erase (fun k hk he => by
        have := hf.lt (hS'S k hk); omega)
  have hBlow : ∀ z : Nat, z < n → B[z]? = s₁.frame[z]? := fun z hz => by
    simp only [B]; rw [erase_get_ne (by omega), insert_get_ne (by omega)]
  have hBhigh : ∀ z : Nat, n ≤ z → B[z]? = none := fun z hz => by
    simp only [B]
    by_cases hzn : n = z
    · subst hzn; exact erase_get_self
    · rw [erase_get_ne hzn, insert_get_ne hzn]; exact hpa.high hf hCsS hz
  let D := armDrops out a b
  let H₀ := B.insert x lu
  let H₁ := if (!mentions a 0) = true then H₀.erase x else H₀
  let H := eraseL H₁ (D.map ρ)
  have hDS' : ∀ d ∈ D, S' d = true := fun d hd => by
    have := armDrops_mem.mp hd
    simp only [Bool.and_eq_true] at this; simp [S', this.1.1]
  let S'' : Nat → Bool := fun k => S' k && !(mentions b (k + 1) && !mentions a (k + 1) && !out k)
  have hfa : FrameOK p N (u :: γ) (cons1 x ρ) m (need a (liftO 1 out)) H := by
    have h₁ := hB.push (x := x) (fun z v hz => by
      by_contra hc; rw [hBhigh z (by omega)] at hz; cases hz) hxm (by omega) hlu (mentions a 0)
    have h₂ := h₁.eraseIf (x := x) (!mentions a 0) (fun hm k hk he => by
      rcases k with _ | k
      · simp only [Bool.not_eq_true'] at hm; simp [hm] at hk
      · simp only [cons1, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at he
        simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at hk
        have := hf.lt (hS'S k hk); omega)
    have h₃ := (h₂.mono (S' := fun jj => if jj = 0 then mentions a 0 else S'' (jj - 1)) (le_refl _)
      (fun jj hjj => by
        rcases jj with _ | k
        · exact hjj
        · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, S'', Bool.and_eq_true] at hjj ⊢
          exact hjj.1)).eraseL (D.map ρ) (fun y hy jj hjj he => by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hy
        rcases jj with _ | k
        · simp only [cons1, if_true] at he
          have := hf.lt (hS'S d (hDS' d hd)); omega
        · simp only [cons1, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at he
          simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, S'', Bool.and_eq_true,
            Bool.not_eq_true'] at hjj
          have hkd := hf.inj k d (hS'S k hjj.1) (hS'S d (hDS' d hd)) he
          subst hkd
          rw [armDrops_mem.mp hd] at hjj; cases hjj.2)
    refine h₃.mono (le_refl _) (fun jj hjj => ?_)
    rcases jj with _ | k
    · simpa [need, liftO] using hjj
    · simp only [need, liftO_add, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at hjj ⊢
      simp only [S'', S']
      revert hjj
      cases mentions a (k + 1) <;> cases mentions b (k + 1) <;> cases out k <;> decide
  obtain ⟨v, s₂, hv, hh₂, hpb, hsb⟩ := iha hN (u :: γ) { s₁ with frame := H } c₁ μ₁ c' μ' w j hj hba
    hfa (hh₁.frame _)
  have hρ1 : ∀ k, cons1 x ρ (k + 1) = ρ k := fun k => by simp [cons1]
  let Cb : Nat → Bool := fun k => (mentions b (k + 1) && !mentions a (k + 1) && !out k) ||
    cons a (liftO 1 out) (k + 1)
  have hCbS : ∀ k, Cb k = true → S k = true := fun k hk => by
    rw [hS]; simp only [Cb, cons, liftO_add, Bool.or_eq_true, Bool.and_eq_true] at hk ⊢; tauto
  have hH : ∀ z, H[z]? = if z ∈ D.map ρ then none else H₁[z]? := fun z => eraseL_get _ _ _
  have hH₁ : ∀ z : Nat, z < n → H₁[z]? = s₁.frame[z]? := fun z hz => by
    simp only [H₁, H₀]
    split
    · rw [erase_get_ne (by omega), insert_get_ne (by omega), hBlow z hz]
    · rw [insert_get_ne (by omega), hBlow z hz]
  refine ⟨v, s₂, hv, hh₂, post_seq (C := C) hf hpa hCsS (G := H₁) hH₁ (fun k hk => ?_)
    (fun z hz hne => ?_) hCbS (fun k => ?_) (fun z _ => rfl) (fun z hz => ?_), fun rt => ?_⟩
  · by_cases hc : cons a (liftO 1 out) (k + 1) = true
    · rw [← hρ1]; exact hpb.1 _ hc
    · have hd : k ∈ D := armDrops_mem.mpr (by simp only [Cb, hc, Bool.or_false] at hk; exact hk)
      by_cases hex : ∃ jj, cons a (liftO 1 out) jj = true ∧ cons1 x ρ jj = ρ k
      · obtain ⟨jj, hjj, he⟩ := hex; rw [← he]; exact hpb.1 _ hjj
      · rw [hpb.2 _ (fun jj hjj he => hex ⟨jj, hjj, he⟩)]
        show H[ρ k]? = none
        rw [hH, if_pos (List.mem_map.mpr ⟨k, hd, rfl⟩)]
  · rw [hpb.2 z (fun jj hjj he => by
      rcases jj with _ | k
      · simp only [cons1, if_true] at he; omega
      · rw [hρ1] at he; exact hne k (by simp [Cb, hjj]) he)]
    show H[z]? = H₁[z]?
    rw [hH, if_neg (fun hm => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm
      exact hne d (by simp only [Cb]; rw [armDrops_mem.mp hd, Bool.true_or]) rfl)]
  · rw [hC, hCsd]
    simp only [Cb, cons, liftO_add]
    cases mentions sv k <;> cases mentions a (k + 1) <;> cases mentions b (k + 1) <;>
      cases out k <;> rfl
  · refine high_none hpb (fun z' hz' hne => ?_) hz
    -- the only variable at or above `n` the arm starts with is the payload's, when it reads it
    have hz'x : z' = x := by
      by_contra hzx
      apply hne
      show H[z']? = none
      rw [hH]; split
      · rfl
      · simp only [H₁, H₀]
        split
        · rw [erase_get_ne (Ne.symm hzx), insert_get_ne (Ne.symm hzx), hBhigh z' hz']
        · rw [insert_get_ne (Ne.symm hzx), hBhigh z' hz']
    subst hz'x
    refine ⟨0, ?_, by simp [cons1]⟩
    cases h0 : mentions a 0
    · exfalso; apply hne
      show H[z']? = none
      rw [hH]; split
      · rfl
      · simp only [H₁, h0, Bool.not_false, if_true]; exact erase_get_self
    · simp [cons, h0, liftO]
  · refine sim_dropIf (hty x (by omega)) (fun _ => ⟨lu, insert_get_self⟩) ?_
    refine sim_dropsT hty (D.map ρ) _ ((armDrops_nodup out a b).map_on (fun d hd d' hd' he =>
      hf.inj d d' (hS'S d (hDS' d hd)) (hS'S d' (hDS' d' hd')) he)) (fun y hy => ?_) (hsb rt)
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hy
    have hρd := hf.lt (hS'S d (hDS' d hd))
    obtain ⟨-, vd, -, hvd, -⟩ := hB.live d (hDS' d hd)
    refine ⟨by omega, vd, ?_⟩
    show H₁[ρ d]? = some vd
    simp only [H₁, H₀]
    split
    · rw [erase_get_ne (by omega), insert_get_ne (by omega)]; exact hvd
    · rw [insert_get_ne (by omega)]; exact hvd

theorem fwd_case {p : Prog} {N sz : Nat} {ρ : Nat → Nat} {n n₁ n₂ n₃ : Nat} {out : Out}
    {sv a b : Expr} {ts ta tb : Tm} (hty : TyOK p N)
    (hs : Pr p N ρ (n + 3) (unionO out (unionO (fvAt 1 a) (fvAt 1 b))) sv ts n₁)
    (ha : Pr p N (cons1 (n + 1) ρ) n₁ (liftO 1 out) a ta n₂)
    (hb : Pr p N (cons1 (n + 2) ρ) n₂ (liftO 1 out) b tb n₃)
    (ihs : FwdOne p N sz ρ (n + 3) (unionO out (unionO (fvAt 1 a) (fvAt 1 b))) sv ts n₁)
    (iha : FwdOne p N sz (cons1 (n + 1) ρ) n₁ (liftO 1 out) a ta n₂)
    (ihb : FwdOne p N sz (cons1 (n + 2) ρ) n₂ (liftO 1 out) b tb n₃) :
    FwdOne p N sz ρ n out (.case sv a b) (.letv n ts (.case n
        (n + 1) (dropIf (!mentions a 0) (n + 1) (dropsT ((armDrops out a b).map ρ) ta))
        (n + 2) (dropIf (!mentions b 0) (n + 2) (dropsT ((armDrops out b a).map ρ) tb)))) n₃ := by
  intro hN γ s c μ c' μ' w kk hk hbig hf hh
  have hn₁ := pr_le hs; have hn₂ := pr_le ha; have hn₃ := pr_le hb
  simp only [Expr.psub] at hbig
  have hfs : FrameOK p N γ ρ (n + 3) (need sv (unionO out (unionO (fvAt 1 a) (fvAt 1 b)))) s.frame :=
    hf.mono (by omega) (fun k hk => by
      simp only [need, unionO, fvAt, mentions, Bool.or_eq_true] at hk ⊢; tauto)
  have hS : ∀ k, need (.case sv a b) out k =
      (mentions sv k || mentions a (k + 1) || mentions b (k + 1) || out k) := fun k => rfl
  have hS' : ∀ k, need (.case sv a b) out k =
      (mentions sv k || mentions b (k + 1) || mentions a (k + 1) || out k) := fun k => by
    simp only [need, mentions]
    cases mentions sv k <;> cases mentions a (k + 1) <;> cases mentions b (k + 1) <;> rfl
  have hCs : ∀ k, cons sv (unionO out (unionO (fvAt 1 a) (fvAt 1 b))) k =
      (mentions sv k && !(out k || mentions a (k + 1) || mentions b (k + 1))) := fun k => by
    simp only [cons, unionO, fvAt, Bool.or_assoc]
  have hCs' : ∀ k, cons sv (unionO out (unionO (fvAt 1 a) (fvAt 1 b))) k =
      (mentions sv k && !(out k || mentions b (k + 1) || mentions a (k + 1))) := fun k => by
    simp only [cons, unionO, fvAt]
    cases mentions a (k + 1) <;> cases mentions b (k + 1) <;> cases out k <;> simp
  have hC : ∀ k, cons (.case sv a b) out k =
      ((mentions sv k || mentions a (k + 1) || mentions b (k + 1)) && !out k) := fun k => rfl
  have hC' : ∀ k, cons (.case sv a b) out k =
      ((mentions sv k || mentions b (k + 1) || mentions a (k + 1)) && !out k) := fun k => by
    simp only [cons, mentions]
    cases mentions sv k <;> cases mentions a (k + 1) <;> cases mentions b (k + 1) <;> rfl
  rcases big_case_inv hbig with ⟨i, j, c₁, μ₁, u, hi, hj, hbv, hba⟩ |
      ⟨i, j, c₁, μ₁, u, hi, hj, hbv, hba⟩
  · rw [psub_arm] at hba
    obtain ⟨vs, s₁, hvs, hh₁, hps, hss⟩ := ihs (by omega) γ s c μ c₁ μ₁ _ i (by omega) hbv hfs hh
    obtain ⟨lu, rfl, hlu⟩ := vrel_inj₁_inv hvs
    obtain ⟨v, s₂, hv, hh₂, hpost, hsim⟩ := fwd_arm (sv := sv) (b := b) (S := need (.case sv a b) out)
      (C := cons (.case sv a b) out) (lv₀ := .inj false lu) (x := n + 1) (m := n₁) (m' := n₂)
      hty (by omega) (by omega)
      hn₂ (by omega) iha hS hCs hC hf hps hlu (by omega) hba hh₁
    exact ⟨v, s₂, hv, hh₂, hpost, fun rt => sim_letv (hty n (by omega)) (hss LTy.unit)
      (sim_case_l (s := { s₁ with frame := s₁.frame.insert n (.inj false lu) }) insert_get_self
        (hsim rt))⟩
  · rw [psub_arm] at hba
    obtain ⟨vs, s₁, hvs, hh₁, hps, hss⟩ := ihs (by omega) γ s c μ c₁ μ₁ _ i (by omega) hbv hfs hh
    obtain ⟨lu, rfl, hlu⟩ := vrel_inj₂_inv hvs
    obtain ⟨v, s₂, hv, hh₂, hpost, hsim⟩ := fwd_arm (sv := sv) (b := a) (S := need (.case sv a b) out)
      (C := cons (.case sv a b) out) (lv₀ := .inj true lu) (x := n + 2) (m := n₂) (m' := n₃)
      hty (by omega) (by omega)
      hn₃ (by omega) ihb hS' hCs' hC' hf hps hlu (by omega) hba hh₁
    exact ⟨v, s₂, hv, hh₂, hpost, fun rt => sim_letv (hty n (by omega)) (hss LTy.unit)
      (sim_case_r (s := { s₁ with frame := s₁.frame.insert n (.inj true lu) }) insert_get_self
        (hsim rt))⟩

/-! #### Closures -/

/-- The copies `envCopies` makes: `vs`'s values at the fresh variables from `m` of the slots the
rest reads. -/
def copyIns (out : Out) : List Nat → Nat → List LV → Std.HashMap Var LV → Std.HashMap Var LV
  | k :: ks, m, v :: vs, F => copyIns out ks (m + 1) vs (if out k then F.insert m v else F)
  | _, _, _, F => F

theorem copyIns_low (out : Out) : ∀ (cs : List Nat) (m : Nat) (vs : List LV)
    (F : Std.HashMap Var LV) (x : Nat), x < m → (copyIns out cs m vs F)[x]? = F[x]?
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, [], _, _, _ => rfl
  | k :: ks, m, v :: vs, F, x, hx => by
      simp only [copyIns]
      rw [copyIns_low out ks (m + 1) vs _ x (by omega)]
      split
      · exact insert_get_ne (by omega)
      · rfl

theorem copyIns_get (out : Out) : ∀ (cs : List Nat) (m : Nat) (vs : List LV)
    (F : Std.HashMap Var LV) (i : Nat), vs.length = cs.length → (hi : i < cs.length) →
    out cs[i] = true → (copyIns out cs m vs F)[m + i]? = vs[i]?
  | [], _, _, _, _, _, hi, _ => absurd hi (by simp)
  | k :: ks, m, v :: vs, F, i, hl, hi, ho => by
      simp only [copyIns]
      cases i with
      | zero =>
          simp only [List.getElem_cons_zero] at ho
          rw [copyIns_low out ks (m + 1) vs _ _ (by omega), if_pos ho]
          simp
      | succ i =>
          rw [show m + (i + 1) = (m + 1) + i by omega]
          exact copyIns_get out ks (m + 1) vs _ i (by simpa using hl) (by simpa using hi)
            (by simpa using ho)
  | _ :: _, _, [], _, _, hl, _, _ => by simp at hl

theorem copyIns_high (out : Out) : ∀ (cs : List Nat) (m : Nat) (vs : List LV)
    (F : Std.HashMap Var LV) (x : Nat), m ≤ x →
    (∀ i (hi : i < cs.length), m + i = x → out cs[i] = false) →
    (copyIns out cs m vs F)[x]? = F[x]?
  | [], _, _, _, _, _, _ => rfl
  | _ :: _, _, [], _, _, _, _ => rfl
  | k :: ks, m, v :: vs, F, x, hx, hno => by
      simp only [copyIns]
      by_cases hxm : x = m
      · subst hxm
        have h0 := hno 0 (by simp) (by simp)
        simp only [List.getElem_cons_zero] at h0
        rw [copyIns_low out ks (x + 1) vs _ x (by omega), if_neg (by simp [h0])]
      · rw [copyIns_high out ks (m + 1) vs _ x (by omega) (fun i hi he => by
          have := hno (i + 1) (by simp; omega) (by omega); simpa using this)]
        split
        · exact insert_get_ne (by omega)
        · rfl

theorem envVars_length (ρ : Nat → Nat) (out : Out) :
    ∀ (cs : List Nat) (m : Nat), (envVars ρ out cs m).length = cs.length
  | [], _ => rfl
  | _ :: ks, m => by simp [envVars, envVars_length ρ out ks (m + 1)]

theorem envVars_get (ρ : Nat → Nat) (out : Out) :
    ∀ (cs : List Nat) (m i : Nat) (hi : i < cs.length),
      (envVars ρ out cs m)[i]'(by rw [envVars_length]; exact hi) =
        if out cs[i] then m + i else ρ cs[i]
  | [], _, _, hi => absurd hi (by simp)
  | k :: ks, m, i, hi => by
      cases i with
      | zero => simp [envVars]
      | succ i =>
          simp only [envVars, List.getElem_cons_succ]
          rw [envVars_get ρ out ks (m + 1) i (by simpa using hi)]
          simp only [show m + 1 + i = m + (i + 1) by omega]

/-- **The copies, then `t`**: `t` runs from the frame with the copies at their fresh
variables. -/
theorem sim_envCopies {p : Prog} {N : Nat} (hty : TyOK p N) {rt : LTy} {T : Tm} {ρ : Nat → Nat}
    {out : Out} {r : Except String (LV × St)} : ∀ (cs : List Nat) (m : Nat) (vs : List LV) (s : St),
    vs.length = cs.length → (∀ i (hi : i < cs.length), s.frame[ρ cs[i]]? = vs[i]?) →
    (∀ k ∈ cs, ρ k < m ∧ ρ k < N) →
    Sim (fun f => Backend2.eval p f rt T) ({ s with frame := copyIns out cs m vs s.frame } : St) r →
    Sim (fun f => Backend2.eval p f rt (envCopies ρ out cs m T)) s r
  | [], _, _, _, _, _, _, h => h
  | _ :: _, _, [], _, hl, _, _, _ => by simp at hl
  | k :: ks, m, v :: vs, s, hl, hv, hρ, h => by
      simp only [envCopies]
      have hv0 : s.frame[ρ k]? = some v := by
        have := hv 0 (by simp)
        simp only [List.getElem_cons_zero, List.getElem?_cons_zero] at this; exact this
      have hρ' : ∀ k' ∈ ks, ρ k' < m + 1 ∧ ρ k' < N := fun k' hk' => by
        have := hρ k' (by simp [hk']); omega
      split
      · refine sim_copy (hty _ (hρ k (by simp)).2) hv0
          (sim_envCopies hty ks (m + 1) vs _ (by simpa using hl) (fun i hi => ?_) hρ' ?_)
        · show (s.frame.insert m v)[ρ ks[i]]? = vs[i]?
          have := hρ ks[i] (by simp)
          rw [insert_get_ne (by omega)]
          have := hv (i + 1) (by simp; omega)
          simp only [List.getElem_cons_succ, List.getElem?_cons_succ] at this; exact this
        · simpa [copyIns, *] using h
      · refine sim_envCopies hty ks (m + 1) vs s (by simpa using hl) (fun i hi => ?_) hρ' ?_
        · have := hv (i + 1) (by simp; omega)
          simp only [List.getElem_cons_succ, List.getElem?_cons_succ] at this; exact this
        · simpa [copyIns, *] using h

theorem exists_vals {F : Std.HashMap Var LV} {ρ : Nat → Nat} : ∀ (cs : List Nat),
    (∀ k ∈ cs, ∃ v, F[ρ k]? = some v) →
    ∃ vs : List LV, vs.length = cs.length ∧ ∀ i (hi : i < cs.length), F[ρ cs[i]]? = vs[i]?
  | [], _ => ⟨[], rfl, fun i hi => absurd hi (by simp)⟩
  | k :: ks, h => by
      obtain ⟨v, hv⟩ := h k (by simp)
      obtain ⟨vs, hl, hg⟩ := exists_vals ks (fun k' hk' => h k' (by simp [hk']))
      refine ⟨v :: vs, by simp [hl], fun i hi => ?_⟩
      cases i with
      | zero => simpa using hv
      | succ i => simpa using hg i (by simpa using hi)

theorem mem_capt {b : Expr} {k : Nat} : k ∈ capt b ↔ mentions b (k + 1) = true := by
  simp only [capt, List.mem_filter, List.mem_range, and_iff_right_iff_imp]
  intro h; have := mentions_lt h; omega

theorem capt_nodup (b : Expr) : (capt b).Nodup := (List.nodup_range).filter _

theorem fwd_lam {p : Prog} {N sz : Nat} (hty : TyOK p N) {ρ : Nat → Nat} {n m : Nat} {out : Out}
    {b : Expr} {tb : Tm} (c : Nat)
    (hb : Pr p N (lamEnv b) ((capt b).length + 1) noOut b tb m) (hm : m ≤ N)
    (hc : CodeAt p c (capt b).length (dropIf (!mentions b 0) (capt b).length tb)) :
    FwdOne p N sz ρ n out (.lam b)
      (envCopies ρ out (capt b) n (.clos c (envVars ρ out (capt b) n))) (n + (capt b).length) := by
  intro hN γ s c₀ μ c' μ' w kk _ hbig hf hh
  simp only [Expr.psub] at hbig
  obtain ⟨rfl, rfl, rfl⟩ := big_val_inv hbig (Val.lam (Expr.psub 1 γ b)) rfl
  have hcapS : ∀ k ∈ capt b, need (.lam b) out k = true := fun k hk => by
    simp [need, mentions, mem_capt.mp hk]
  obtain ⟨vs, hvl, hvs⟩ := exists_vals (F := s.frame) (ρ := ρ) (capt b) (fun k hk => by
    obtain ⟨_, v, _, hv, _⟩ := hf.live k (hcapS k hk); exact ⟨v, hv⟩)
  let ev := envVars ρ out (capt b) n
  let Fc := copyIns out (capt b) n vs s.frame
  have hevl : ev.length = (capt b).length := envVars_length ρ out (capt b) n
  have hev : ∀ i (hi : i < (capt b).length), ev[i]'(by omega) =
      if out (capt b)[i] then n + i else ρ (capt b)[i] := fun i hi => envVars_get ρ out (capt b) n i hi
  have hρn : ∀ k ∈ (capt b), ρ k < n := fun k hk => hf.lt (hcapS k hk)
  have hFc : ∀ i (hi : i < (capt b).length), Fc[ev[i]'(by omega)]? = vs[i]? := by
    intro i hi
    rw [hev i hi]
    split
    · exact copyIns_get out (capt b) n vs s.frame i hvl hi (by assumption)
    · rw [copyIns_low out (capt b) n vs s.frame _ (hρn _ (List.getElem_mem hi))]; exact hvs i hi
  have hnd : ev.Nodup := by
    rw [List.nodup_iff_injective_get]
    intro ⟨i, hi⟩ ⟨j, hj⟩ he
    simp only [List.get_eq_getElem] at he
    have hi' : i < (capt b).length := by omega
    have hj' : j < (capt b).length := by omega
    rw [hev i hi', hev j hj'] at he
    have hρi := hρn _ (List.getElem_mem hi'); have hρj := hρn _ (List.getElem_mem hj')
    simp only [Fin.mk.injEq]
    split at he <;> split at he
    · omega
    · omega
    · omega
    · have := hf.inj _ _ (hcapS _ (List.getElem_mem hi')) (hcapS _ (List.getElem_mem hj')) he
      exact (List.Nodup.getElem_inj_iff (capt_nodup b)).mp this
  obtain ⟨vs', hrun, hlen', hget⟩ := takeAll_run ev { s with frame := Fc } hnd (fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < (capt b).length := by omega
    have := hFc i hi'
    rw [List.getElem?_eq_getElem (by omega)] at this
    exact ⟨_, this⟩)
  have hvs' : vs' = vs := by
    apply List.ext_getElem (by rw [hlen', hvl]; exact hevl)
    intro i h₁ h₂
    have hi' : i < (capt b).length := by omega
    have := hget i (by omega)
    rw [show (({ s with frame := Fc } : St)).frame = Fc from rfl, hFc i hi',
      List.getElem?_eq_getElem h₂, List.getElem?_eq_getElem h₁] at this
    exact (Option.some.inj this).symm
  rw [hvs'] at hrun
  refine ⟨.clos c vs, { s with frame := eraseL Fc ev }, ?_, hh.frame _, ⟨fun k hk => ?_, fun x hx => ?_⟩, ?_⟩
  · refine .lam hb hm hc hvl (fun k hk => ?_) (fun i hi k hk hik => ?_)
    · obtain ⟨w, _, hw, _⟩ := hf.live k (hcapS k hk)
      exact (List.getElem?_eq_some_iff.mp hw).1
    · have hi' : i < (capt b).length := by omega
      have hk' : (capt b)[i] = k := by simpa [List.getElem?_eq_getElem hi'] using hik
      obtain ⟨w', v', hw', hv', hr'⟩ := hf.live k (hcapS k (hk' ▸ List.getElem_mem hi'))
      have e1 : γ[k] = w' := by rw [List.getElem?_eq_some_iff] at hw'; exact hw'.2
      have e2 := hvs i hi'
      rw [hk', hv', List.getElem?_eq_getElem hi] at e2
      cases e2
      rw [e1]; exact hr'
  · have hkc : k ∈ (capt b) := mem_capt.mpr (by simp [cons, mentions] at hk; exact hk.1)
    have hko : out k = false := by simp [cons] at hk; exact hk.2
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hkc
    show (eraseL Fc ev)[ρ (capt b)[i]]? = none
    rw [eraseL_get, if_pos]
    have := hev i hi
    rw [hko, if_neg (by simp)] at this
    rw [← this]; exact List.getElem_mem _
  · show (eraseL Fc ev)[x]? = s.frame[x]?
    rw [eraseL_get]
    split
    · rename_i hxe
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hxe
      have hi' : i < (capt b).length := by omega
      rw [hev i hi']
      split
      · rename_i ho
        symm; exact fresh_none hf (by omega)
      · rename_i ho
        exact absurd (by rw [hev i hi', if_neg ho]) (hx (capt b)[i]
          (by simp [cons, mentions, mem_capt.mp (List.getElem_mem hi'), ho]))
    · rename_i hxe
      by_cases hxn : x < n
      · exact copyIns_low out (capt b) n vs s.frame x hxn
      · refine copyIns_high out (capt b) n vs s.frame x (by omega) (fun i hi he => ?_)
        by_contra ho
        apply hxe
        have := hev i hi
        rw [if_pos (by simpa using ho)] at this
        rw [← he, ← this]; exact List.getElem_mem _
  · intro rt
    refine sim_envCopies hty (capt b) n vs s hvl hvs (fun k hk => ⟨hρn k hk, by have := hρn k hk; omega⟩) ?_
    exact sim_clos hrun

/-! #### Applications -/

/-- **The simulation of a call**, at derivations of size at most `sz`: a head step of the source
on a function and an argument, then a run of its result to `w`, is followed by the interpreter's
call of the corresponding closure on the corresponding argument, which answers a value
corresponding to `w` and leaves the caller's frame. -/
def CallAt (p : Prog) (N sz : Nat) : Prop :=
  ∀ (vf va : Val) (lf la : LV) (s : St) (c : Nat) (μ : Heap) (c₁ : Nat) (μ₁ : Heap) (r : Expr)
    (c' : Nat) (μ' : Heap) (w : Val) (k : Nat), k ≤ sz →
    AHead (ℍ := Backend2.lirHost) bumpAlloc c μ (.app vf.1 va.1) c₁ μ₁ r →
    BigN (ℍ := Backend2.lirHost) bumpAlloc k c₁ μ₁ r c' μ' w →
    VRel p N vf lf → VRel p N va la → HRel p N c μ s →
    ∃ lw s', VRel p N w lw ∧ HRel p N c' μ' s' ∧ s'.frame = s.frame ∧
      Sim (fun f => Backend2.callClos p f lf (some la) 0) s (.ok (lw, s'))

theorem Post.congr {C : Nat → Bool} {ρ : Nat → Nat} {F F' F'' : Std.HashMap Var LV}
    (h : Post C ρ F F') (he : ∀ x : Nat, F''[x]? = F'[x]?) : Post C ρ F F'' :=
  ⟨fun k hk => by rw [he]; exact h.1 k hk, fun x hx => by rw [he]; exact h.2 x hx⟩

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

theorem isEmpty_of_none {F : Std.HashMap Var LV} (h : ∀ x : Nat, F[x]? = none) : F.isEmpty = true := by
  rw [Std.HashMap.isEmpty_iff_forall_not_mem]
  intro x hx
  rw [Std.HashMap.mem_iff_isSome_getElem?, h x] at hx
  simp at hx

/-- **A call of a code**: its function's frame its parameters at the arguments; when its body
runs to `v` and an empty frame, the call answers `v` with the caller's frame. -/
theorem sim_code {p : Prog} {c k : Nat} {body : Tm} (hc : CodeAt p c k body) {args : List LV}
    (hlen : args.length = k + 1) {s s' : St} {v : LV}
    (hb : ∀ rt : LTy, Sim (fun f => Backend2.eval p f rt body)
      ({ s with frame := ((List.range (k + 1)).zip args).foldl (fun m x => m.insert x.1 x.2) ∅ } : St)
      (.ok (v, s')))
    (hempty : ∀ x : Nat, s'.frame[x]? = none) :
    Sim (fun f => Backend2.callFn p f c args) s (.ok (v, ({ s' with frame := s.frame } : St))) := by
  obtain ⟨-, fn, hfn, hpar, hbody⟩ := hc
  refine sim_callFn hfn (by rw [hpar, hlen]; simp) ?_ (isEmpty_of_none hempty)
  rw [hpar, hbody]; exact hb fn.ret

theorem zip1 (la : LV) :
    (((List.range (0 + 1)).zip [la]).foldl (fun m x => m.insert x.1 x.2) (∅ : Std.HashMap Var LV)) =
      (∅ : Std.HashMap Var LV).insert 0 la := rfl

/-- **`store ℓ`**: the closure of `store1Code` on `ℓ`. -/
theorem call_store0 {p : Prog} {N : Nat} (hrt : RT p N) (la : LV) (s : St) :
    Sim (fun f => Backend2.callClos p f (.clos 3 []) (some la) 0) s
      (.ok (.clos store1Code [la], s)) := by
  refine sim_callClos hrt.store0.1 ?_
  have h := sim_code (s := s) (args := [] ++ [la]) hrt.store0 rfl
    (s' := { s with frame := ((∅ : Std.HashMap Var LV).insert 0 la).erase 0 })
    (fun rt => by
      rw [show (([] : List LV) ++ [la]) = [la] from rfl, zip1]
      exact sim_clos (env := [0]) (takeAll_one_run (s := { s with frame := (∅ : Std.HashMap Var LV).insert 0 la })
        insert_get_self))
    (fun x => by
      show (((∅ : Std.HashMap Var LV).insert 0 la).erase 0)[x]? = none
      by_cases hx : 0 = x
      · subst hx; exact erase_get_self
      · rw [erase_get_ne hx, insert_get_ne hx]; simp)
  exact h

theorem vrel_store_inv {p : Prog} {N : Nat} {lv : LV} (h : VRel p N (Val.prim .store) lv) :
    lv = .clos 3 [] := by
  generalize hV : Val.prim .store = V at h
  cases h with
  | rt q c hc =>
      have e := congrArg Subtype.val hV
      simp only [Val.prim, Expr.prim.injEq] at e
      subst e; simp [rtCode] at hc; subst hc; rfl
  | _ => have e := congrArg Subtype.val hV; simp [Val.pair, Val.unit, Val.prim, Val.inj₁,
      Val.inj₂, Val.lam, Val.loc, Val.storeV] at e

theorem fwd_app {p : Prog} {N sz : Nat} {ρ : Nat → Nat} {n n₁ n₂ : Nat} {out : Out} {f a : Expr}
    {ta tf : Tm} (hty : TyOK p N) (hrt : RT p N)
    (ha : Pr p N ρ (n + 2) (unionO out (fvAt 0 f)) a ta n₁) (hf' : Pr p N ρ n₁ out f tf n₂)
    (iha : FwdOne p N sz ρ (n + 2) (unionO out (fvAt 0 f)) a ta n₁)
    (ihf : FwdOne p N sz ρ n₁ out f tf n₂) (hcall : ∀ m, m < sz → CallAt p N m) :
    FwdOne p N sz ρ n out (.app f a) (.letv n ta (.letv (n + 1) tf (.app (n + 1) n))) n₂ := by
  intro hN γ s c μ c' μ' w kk hk hbig hf hh
  have hn₁ := pr_le ha; have hn₂ := pr_le hf'
  simp only [Expr.psub] at hbig
  have hfa : FrameOK p N γ ρ (n + 2) (need a (unionO out (fvAt 0 f))) s.frame :=
    hf.mono (by omega) (fun k hk => by
      simp only [need, unionO, fvAt, mentions, Nat.add_zero, Bool.or_eq_true] at hk ⊢; tauto)
  have hCa : ∀ k, cons a (unionO out (fvAt 0 f)) k = true → need (.app f a) out k = true := by
    intro k hk
    simp only [cons, need, unionO, fvAt, mentions, Nat.add_zero, Bool.or_eq_true, Bool.and_eq_true,
      Bool.not_eq_true'] at hk ⊢; tauto
  have hCf : ∀ k, cons f out k = true → need (.app f a) out k = true := fun k hk => by
    simp only [cons, need, mentions, Bool.or_eq_true, Bool.and_eq_true] at hk ⊢; tauto
  have hC : ∀ k, cons (.app f a) out k = (cons a (unionO out (fvAt 0 f)) k || cons f out k) := by
    intro k
    simp only [cons, unionO, fvAt, mentions, Nat.add_zero]
    cases mentions a k <;> cases mentions f k <;> cases out k <;> rfl
  -- the two parts, in the machine's order
  have parts : ∀ {c₁ c₂ : Nat} {μ₁ μ₂ : Heap} {va vf : Val} {i j : Nat}, i ≤ kk → j ≤ kk →
      BigN (ℍ := Backend2.lirHost) bumpAlloc i c μ (Expr.psub 0 γ a) c₁ μ₁ va →
      BigN (ℍ := Backend2.lirHost) bumpAlloc j c₁ μ₁ (Expr.psub 0 γ f) c₂ μ₂ vf →
      ∃ la lf s₁ s₂, VRel p N va la ∧ VRel p N vf lf ∧ HRel p N c₂ μ₂ s₂ ∧
        Post (cons (.app f a) out) ρ s.frame (((s₂.frame.insert (n + 1) lf).erase (n + 1)).erase n) ∧
        s₂.frame[n]? = some la ∧
        Sim (fun g => Backend2.eval p g LTy.unit ta) s (.ok (la, s₁)) ∧
        Sim (fun g => Backend2.eval p g LTy.unit tf) { s₁ with frame := s₁.frame.insert n la }
          (.ok (lf, s₂)) := by
    intro c₁ c₂ μ₁ μ₂ va vf i j hi hj hba hbf
    obtain ⟨la, s₁, hla, hh₁, hpa, hsa⟩ := iha (by omega) γ s c μ c₁ μ₁ va i (by omega) hba hfa hh
    have hff : FrameOK p N γ ρ n₁ (need f out) (s₁.frame.insert n la) :=
      hf.after hpa hCa (le_refl n) (by omega) (fun k hk => by
        simp only [cons, need, unionO, fvAt, mentions, Nat.add_zero, Bool.or_eq_true,
          Bool.and_eq_false_iff, Bool.not_eq_false'] at hk ⊢
        exact ⟨by tauto, by tauto⟩)
    obtain ⟨lf, s₂, hlf, hh₂, hpf, hsf⟩ := ihf (by omega) γ { s₁ with frame := s₁.frame.insert n la }
      c₁ μ₁ c₂ μ₂ vf j (by omega) hbf hff (hh₁.frame _)
    obtain ⟨hn, hpost⟩ := post_seq2 (C := cons (.app f a) out) (vb := lf) hf hpa hCa hpf hCf hC
    refine ⟨la, lf, s₁, s₂, hla, hlf, hh₂, hpost.congr (fun x => ?_), hn, hsa LTy.unit, hsf LTy.unit⟩
    by_cases h1 : n + 1 = x
    · subst h1; rw [erase_get_ne (by omega), erase_get_self, erase_get_self]
    by_cases h2 : n = x
    · subst h2; rw [erase_get_self, erase_get_ne (by omega), erase_get_self]
    rw [erase_get_ne h2, erase_get_ne h1, erase_get_ne h1, erase_get_ne h2]
  rcases big_app_inv hbig with
      ⟨i, j, k, c₁, μ₁, c₂, μ₂, c₃, μ₃, va, vf, r, hi, hj, hk', hba, hbf, hhd, hbr⟩ |
      ⟨i, j, c₁, μ₁, va, hi, hj, hba, hbf, rfl⟩
  · obtain ⟨la, lf, s₁, s₂, hla, hlf, hh₂, hpost, hn, hsa, hsf⟩ := parts hi hj hba hbf
    let s₂' : St := { s₂ with frame := ((s₂.frame.insert (n + 1) lf).erase (n + 1)).erase n }
    obtain ⟨lw, s₃, hlw, hh₃, hfr, hsc⟩ := hcall k (by omega) vf va lf la s₂' c₂ μ₂ c₃ μ₃ r c' μ' w k
      (le_refl k) hhd hbr hlf hla (hh₂.frame _)
    refine ⟨lw, s₃, hlw, hh₃, by rw [hfr]; exact hpost, fun rt => ?_⟩
    refine sim_letv (hty n (by omega)) hsa (sim_letv (hty (n + 1) (by omega)) hsf ?_)
    exact sim_app (s := { s₂ with frame := s₂.frame.insert (n + 1) lf }) insert_get_self
      (by show ((s₂.frame.insert (n + 1) lf).erase (n + 1))[n]? = some la
          rw [erase_get_ne (by omega), insert_get_ne (by omega)]; exact hn) hsc
  · obtain ⟨la, lf, s₁, s₂, hla, hlf, hh₂, hpost, hn, hsa, hsf⟩ := parts hi hj hba hbf
    obtain rfl := vrel_store_inv hlf
    let F' := ((s₂.frame.insert (n + 1) (.clos 3 [])).erase (n + 1)).erase n
    refine ⟨.clos store1Code [la], { s₂ with frame := F' }, .store1 hla, hh₂.frame _, hpost,
      fun rt => ?_⟩
    refine sim_letv (hty n (by omega)) hsa (sim_letv (hty (n + 1) (by omega)) hsf ?_)
    exact sim_app (s := { s₂ with frame := s₂.frame.insert (n + 1) (.clos 3 []) }) insert_get_self
      (by show ((s₂.frame.insert (n + 1) (.clos 3 [])).erase (n + 1))[n]? = some la
          rw [erase_get_ne (by omega), insert_get_ne (by omega)]; exact hn) (call_store0 hrt la _)

end Lowering
