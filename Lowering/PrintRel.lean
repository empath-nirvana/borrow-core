import Lowering.LIRPrint

/-!
# Lowering — the print as a relation  `[spec §56]`

`Pr p N ρ n out e t n'`: `t` is a print of `e` at `ρ`, the slots `out` read after it, its own
variables from `n` below `n'`, its codes those of the final program `p`, each function's variables
below `N`. `prG_pr` says the print's output is in it, over any program holding the tables it wrote;
`lirOf_pr` says it of `lirOf e`'s `main`. `RT p` holds the primitives' codes (`rtBodies`,
`fixBody`'s), which `lirOf` writes first (`lirOf_rt`).
-/

namespace Lowering
open BoCa
open Backend2 (Var Tm Fn Code CodeKind Prog LTy LCTy Op)

/-- The code `c` of `p` is a `λ` code whose function, at `c`, has the parameters `0, …, k` and the
body `t`. -/
def CodeAt (p : Prog) (c k : Nat) (t : Tm) : Prop :=
  p.codes[c]? = some (lamCode c) ∧
    ∃ fn : Fn, p.fns[c]? = some fn ∧ fn.params = List.range (k + 1) ∧ fn.body = t

/-- **The print, as a relation.** -/
inductive Pr (p : Prog) (N : Nat) : (Nat → Nat) → Nat → Out → Expr → Tm → Nat → Prop where
  | varCopy (ρ : Nat → Nat) (n : Nat) (out : Out) (k : Nat) (h : out k = true) :
      Pr p N ρ n out (.var k) (.copy (ρ k) n (.var n)) (n + 1)
  | varMove (ρ : Nat → Nat) (n : Nat) (out : Out) (k : Nat) (h : out k = false) :
      Pr p N ρ n out (.var k) (.var (ρ k)) n
  | unit (ρ : Nat → Nat) (n : Nat) (out : Out) : Pr p N ρ n out .unit .unit n
  | loc (ρ : Nat → Nat) (n : Nat) (out : Out) (ℓ : Loc) :
      Pr p N ρ n out (.loc ℓ) (.prim (.locAt ℓ) []) n
  | lit (ρ : Nat → Nat) (n : Nat) (out : Out) (c : IntLit) :
      Pr p N ρ n out (.prim (.lit c)) (.lit c) n
  | hostV (ρ : Nat → Nat) (n : Nat) (out : Out) (op : HostOp) (c : Nat)
      (h : CodeAt p c 0 (hostFn op)) : Pr p N ρ n out (.prim (.host op)) (.clos c []) n
  | rtV (ρ : Nat → Nat) (n : Nat) (out : Out) (q : Prim) (c : Nat) (h : rtCode q = some c) :
      Pr p N ρ n out (.prim q) (.clos c []) n
  | pair {ρ : Nat → Nat} {n n₁ n₂ : Nat} {out : Out} {a b : Expr} {ta tb : Tm}
      (ha : Pr p N ρ (n + 2) (unionO out (fvAt 0 b)) a ta n₁) (hb : Pr p N ρ n₁ out b tb n₂) :
      Pr p N ρ n out (.pair a b) (.letv n ta (.letv (n + 1) tb (.pair n (n + 1)))) n₂
  | inj₁ {ρ : Nat → Nat} {n n₁ : Nat} {out : Out} {a : Expr} {ta : Tm}
      (ha : Pr p N ρ (n + 1) out a ta n₁) : Pr p N ρ n out (.inj₁ a) (.letv n ta (.inj false n)) n₁
  | inj₂ {ρ : Nat → Nat} {n n₁ : Nat} {out : Out} {a : Expr} {ta : Tm}
      (ha : Pr p N ρ (n + 1) out a ta n₁) : Pr p N ρ n out (.inj₂ a) (.letv n ta (.inj true n)) n₁
  | seq {ρ : Nat → Nat} {n n₁ n₂ : Nat} {out : Out} {a b : Expr} {ta tb : Tm}
      (ha : Pr p N ρ (n + 1) (unionO out (fvAt 0 b)) a ta n₁) (hb : Pr p N ρ n₁ out b tb n₂) :
      Pr p N ρ n out (.seq a b) (.letv n ta (.drop n tb)) n₂
  | app {ρ : Nat → Nat} {n n₁ n₂ : Nat} {out : Out} {f a : Expr} {ta tf : Tm}
      (ha : Pr p N ρ (n + 2) (unionO out (fvAt 0 f)) a ta n₁) (hf : Pr p N ρ n₁ out f tf n₂) :
      Pr p N ρ n out (.app f a) (.letv n ta (.letv (n + 1) tf (.app (n + 1) n))) n₂
  | letpair {ρ : Nat → Nat} {n n₁ n₂ : Nat} {out : Out} {a b : Expr} {ta tb : Tm}
      (ha : Pr p N ρ (n + 3) (unionO out (fvAt 2 b)) a ta n₁)
      (hb : Pr p N (cons2 (n + 2) (n + 1) ρ) n₁ (liftO 2 out) b tb n₂) :
      Pr p N ρ n out (.letpair a b) (.letv n ta (.letpair (n + 1) (n + 2) n
        (dropIf (!mentions b 1) (n + 1) (dropIf (!mentions b 0) (n + 2) tb)))) n₂
  | case {ρ : Nat → Nat} {n n₁ n₂ n₃ : Nat} {out : Out} {s a b : Expr} {ts ta tb : Tm}
      (hs : Pr p N ρ (n + 3) (unionO out (unionO (fvAt 1 a) (fvAt 1 b))) s ts n₁)
      (ha : Pr p N (cons1 (n + 1) ρ) n₁ (liftO 1 out) a ta n₂)
      (hb : Pr p N (cons1 (n + 2) ρ) n₂ (liftO 1 out) b tb n₃) :
      Pr p N ρ n out (.case s a b) (.letv n ts (.case n
        (n + 1) (dropIf (!mentions a 0) (n + 1) (dropsT ((armDrops out a b).map ρ) ta))
        (n + 2) (dropIf (!mentions b 0) (n + 2) (dropsT ((armDrops out b a).map ρ) tb)))) n₃
  | lam {ρ : Nat → Nat} {n m : Nat} {out : Out} {b : Expr} {tb : Tm} (c : Nat)
      (hb : Pr p N (lamEnv b) ((capt b).length + 1) noOut b tb m) (hm : m ≤ N)
      (hc : CodeAt p c (capt b).length (dropIf (!mentions b 0) (capt b).length tb)) :
      Pr p N ρ n out (.lam b) (envCopies ρ out (capt b) n (.clos c (envVars ρ out (capt b) n)))
        (n + (capt b).length)

theorem pr_le {p : Prog} {N : Nat} {ρ : Nat → Nat} {n n' : Nat} {out : Out} {e : Expr} {t : Tm}
    (h : Pr p N ρ n out e t n') : n ≤ n' := by
  induction h <;> omega

/-! ### The print is in the relation -/

/-- `s'` extends `s`: its tables have `s`'s as a prefix, and its bound is at least `s`'s. -/
def Grows (s s' : PS) : Prop :=
  s.fns.size ≤ s'.fns.size ∧
    (∀ i, i < s.fns.size → s'.fns[i]? = s.fns[i]? ∧ s'.codes[i]? = s.codes[i]?) ∧
    s.bound ≤ s'.bound

/-- The program `p` holds the tables of `s`. -/
def Ext (p : Prog) (s : PS) : Prop :=
  ∀ i, i < s.fns.size → p.fns[i]? = s.fns[i]? ∧ p.codes[i]? = s.codes[i]?

theorem Grows.refl (s : PS) : Grows s s := ⟨le_refl _, fun _ _ => ⟨rfl, rfl⟩, le_refl _⟩

theorem Grows.trans {s₁ s₂ s₃ : PS} (h₁ : Grows s₁ s₂) (h₂ : Grows s₂ s₃) : Grows s₁ s₃ :=
  ⟨h₁.1.trans h₂.1, fun i hi => ⟨(h₂.2.1 i (by have := h₁.1; omega)).1.trans (h₁.2.1 i hi).1,
    (h₂.2.1 i (by have := h₁.1; omega)).2.trans (h₁.2.1 i hi).2⟩, h₁.2.2.trans h₂.2.2⟩

theorem Ext.mono {p : Prog} {s s' : PS} (h : Ext p s') (hg : Grows s s') : Ext p s :=
  fun i hi => ⟨(h i (by have := hg.1; omega)).1.trans (hg.2.1 i hi).1,
    (h i (by have := hg.1; omega)).2.trans (hg.2.1 i hi).2⟩

theorem emit_spec (k : Nat) (body : Tm) (m : Nat) (s : PS) (hs : s.fns.size = s.codes.size) :
    let r := emit k body m s
    r.1 = s.fns.size ∧ r.2.fns.size = r.2.codes.size ∧ r.2.fns.size = s.fns.size + 1 ∧
      Grows s r.2 ∧ m ≤ r.2.bound ∧ ∀ p, Ext p r.2 → CodeAt p r.1 k body := by
  simp only [emit]
  refine ⟨trivial, by simp [hs], by simp, ⟨by simp, fun i hi => ?_, by simp⟩, by simp, fun p hp => ?_⟩
  · simp [Array.getElem?_push, hi.ne, hs ▸ hi.ne]
  · have h := hp s.fns.size (by simp)
    exact ⟨by rw [h.2]; simp [hs], lamFn k body, by rw [h.1]; simp, rfl, rfl⟩

/-- A primitive's code: an effect-free primitive that is not a literal or a host operation has
one. -/
theorem rtCode_of_effFree {q : Prim} (h : effPrim q = false) (hl : ∀ c, q ≠ .lit c)
    (hh : ∀ op, q ≠ .host op) : ∃ c, rtCode q = some c := by
  cases q <;> simp_all [effPrim, rtCode]

/-- What the print's induction carries: the tables grow, keeping one code per function, and over
any program holding the final tables, with every function's variables below `N`, the output is
a print of the term. -/
def PrOK (ρ : Nat → Nat) (n : Nat) (out : Out) (e : Expr) (s : PS) (r : (Tm × Nat) × PS) : Prop :=
  r.2.fns.size = r.2.codes.size ∧ Grows s r.2 ∧
    ∀ p N, Ext p r.2 → r.2.bound ≤ N → Pr p N ρ n out e r.1.1 r.1.2

/-- **The print is in the relation**, on effect-free terms. -/
theorem prG_pr : ∀ (e : Expr) (ρ : Nat → Nat) (n : Nat) (out : Out) (s : PS), effFreeB e = true →
    s.fns.size = s.codes.size → PrOK ρ n out e s (prG ρ n out e s) := by
  intro e
  induction e with
  | var k =>
      intro ρ n out s _ hs
      cases hk : out k
      · have : prG ρ n out (.var k) s = ((.var (ρ k), n), s) := by simp [prG, hk]; rfl
        rw [this]; exact ⟨hs, Grows.refl s, fun p N _ _ => .varMove ρ n out k hk⟩
      · have : prG ρ n out (.var k) s = ((.copy (ρ k) n (.var n), n + 1), s) := by
          simp [prG, hk]; rfl
        rw [this]; exact ⟨hs, Grows.refl s, fun p N _ _ => .varCopy ρ n out k hk⟩
  | unit => intro ρ n out s _ hs; exact ⟨hs, Grows.refl s, fun p N _ _ => .unit ρ n out⟩
  | loc ℓ => intro ρ n out s _ hs; exact ⟨hs, Grows.refl s, fun p N _ _ => .loc ρ n out ℓ⟩
  | prim q =>
      intro ρ n out s hc hs
      simp only [effFreeB, Bool.not_eq_true'] at hc
      by_cases hl : ∃ c, q = .lit c
      · obtain ⟨c, rfl⟩ := hl
        exact ⟨hs, Grows.refl s, fun p N _ _ => .lit ρ n out c⟩
      by_cases hh : ∃ op, q = .host op
      · obtain ⟨op, rfl⟩ := hh
        obtain ⟨h0, h1, -, g1, -, c1⟩ := emit_spec 0 (hostFn op) 1 s hs
        exact ⟨h1, g1, fun p N hp _ => .hostV ρ n out op _ (c1 p hp)⟩
      simp only [not_exists] at hl hh
      obtain ⟨c, hcq⟩ := rtCode_of_effFree hc hl hh
      have : prG ρ n out (.prim q) s = ((.clos c [], n), s) := by
        cases q <;> simp_all [prG, primT, rtCode] <;> rfl
      rw [this]
      exact ⟨hs, Grows.refl s, fun p N _ _ => .rtV ρ n out q c hcq⟩
  | pair a b iha ihb | seq a b iha ihb | app a b iha ihb =>
      intro ρ n out s hc hs
      simp only [effFreeB, Bool.and_eq_true] at hc
      first
      | (obtain ⟨h1, g1, p1⟩ := iha ρ (n + 2) (unionO out (fvAt 0 b)) s hc.1 hs
         obtain ⟨h2, g2, p2⟩ := ihb ρ (prG ρ (n + 2) (unionO out (fvAt 0 b)) a s).1.2 out _ hc.2 h1
         exact ⟨h2, g1.trans g2, fun p N hp hN =>
           .pair (p1 p N (hp.mono g2) (g2.2.2.trans hN)) (p2 p N hp hN)⟩)
      | (obtain ⟨h1, g1, p1⟩ := iha ρ (n + 1) (unionO out (fvAt 0 b)) s hc.1 hs
         obtain ⟨h2, g2, p2⟩ := ihb ρ (prG ρ (n + 1) (unionO out (fvAt 0 b)) a s).1.2 out _ hc.2 h1
         exact ⟨h2, g1.trans g2, fun p N hp hN =>
           .seq (p1 p N (hp.mono g2) (g2.2.2.trans hN)) (p2 p N hp hN)⟩)
      | (obtain ⟨h1, g1, p1⟩ := ihb ρ (n + 2) (unionO out (fvAt 0 a)) s hc.2 hs
         obtain ⟨h2, g2, p2⟩ := iha ρ (prG ρ (n + 2) (unionO out (fvAt 0 a)) b s).1.2 out _ hc.1 h1
         exact ⟨h2, g1.trans g2, fun p N hp hN =>
           .app (p1 p N (hp.mono g2) (g2.2.2.trans hN)) (p2 p N hp hN)⟩)
  | inj₁ a ih | inj₂ a ih =>
      intro ρ n out s hc hs
      obtain ⟨h1, g1, p1⟩ := ih ρ (n + 1) out s hc hs
      first
      | exact ⟨h1, g1, fun p N hp hN => .inj₁ (p1 p N hp hN)⟩
      | exact ⟨h1, g1, fun p N hp hN => .inj₂ (p1 p N hp hN)⟩
  | letpair a b iha ihb =>
      intro ρ n out s hc hs
      simp only [effFreeB, Bool.and_eq_true] at hc
      obtain ⟨h1, g1, p1⟩ := iha ρ (n + 3) (unionO out (fvAt 2 b)) s hc.1 hs
      obtain ⟨h2, g2, p2⟩ := ihb (cons2 (n + 2) (n + 1) ρ)
        (prG ρ (n + 3) (unionO out (fvAt 2 b)) a s).1.2 (liftO 2 out) _ hc.2 h1
      exact ⟨h2, g1.trans g2, fun p N hp hN =>
        .letpair (p1 p N (hp.mono g2) (g2.2.2.trans hN)) (p2 p N hp hN)⟩
  | case v a b ihv iha ihb =>
      intro ρ n out s hc hs
      simp only [effFreeB, Bool.and_eq_true] at hc
      obtain ⟨h1, g1, p1⟩ := ihv ρ (n + 3) (unionO out (unionO (fvAt 1 a) (fvAt 1 b))) s hc.1.1 hs
      obtain ⟨h2, g2, p2⟩ := iha (cons1 (n + 1) ρ)
        (prG ρ (n + 3) (unionO out (unionO (fvAt 1 a) (fvAt 1 b))) v s).1.2 (liftO 1 out) _ hc.1.2 h1
      obtain ⟨h3, g3, p3⟩ := ihb (cons1 (n + 2) ρ)
        (prG (cons1 (n + 1) ρ) (prG ρ (n + 3) (unionO out (unionO (fvAt 1 a) (fvAt 1 b))) v s).1.2
          (liftO 1 out) a (prG ρ (n + 3) (unionO out (unionO (fvAt 1 a) (fvAt 1 b))) v s).2).1.2
        (liftO 1 out) _ hc.2 h2
      exact ⟨h3, g1.trans (g2.trans g3), fun p N hp hN =>
        .case (p1 p N ((hp.mono g3).mono g2) (g2.2.2.trans (g3.2.2.trans hN)))
          (p2 p N (hp.mono g3) (g3.2.2.trans hN)) (p3 p N hp hN)⟩
  | lam b ih =>
      intro ρ n out s hc hs
      simp only [effFreeB] at hc
      obtain ⟨h1, g1, p1⟩ := ih (lamEnv b) ((capt b).length + 1) noOut s hc hs
      obtain ⟨-, h2, -, g2, hm, c2⟩ := emit_spec (capt b).length
        (dropIf (!mentions b 0) (capt b).length
          (prG (lamEnv b) ((capt b).length + 1) noOut b s).1.1)
        (prG (lamEnv b) ((capt b).length + 1) noOut b s).1.2 _ h1
      exact ⟨h2, g1.trans g2, fun p N hp hN =>
        .lam _ (p1 p N (hp.mono g2) (g2.2.2.trans hN)) (hm.trans hN) (c2 p hp)⟩

end Lowering

namespace Lowering
open BoCa
open Backend2 (Var Tm Fn Code CodeKind Prog LTy LCTy Op)

/-- The primitives' hand-written codes, written. -/
def rtPS : PS := rtBodies.foldl (fun s kt => (emit kt.1 kt.2 rtBound s).2) {}

theorem preludePS_eq : preludePS = ((prG (fun _ => 0) 0 noOut (.lam fixBody)) rtPS).2 := rfl

theorem rtPS_size : rtPS.fns.size = 14 ∧ rtPS.codes.size = 14 ∧ rtPS.bound = rtBound := by
  refine ⟨rfl, rfl, rfl⟩

/-- **The primitives' codes**, at `rtCode`'s indices and the helpers', and `fixBody`'s, which
the print writes. -/
structure RT (p : Prog) (N : Nat) : Prop where
  alloc : CodeAt p 0 0 allocB
  free : CodeAt p 1 0 freeB
  load : CodeAt p 2 0 loadB
  store0 : CodeAt p 3 0 store0B
  store1 : CodeAt p store1Code 1 store1B
  idx : CodeAt p 5 0 idxB
  split : CodeAt p 6 0 splitB
  tab : CodeAt p 7 0 tabB
  tabLoop : CodeAt p tabLoopCode 4 tabLoopB
  drop : CodeAt p 9 0 dropB
  dropLoop : CodeAt p dropLoopCode 3 dropLoopB
  count : CodeAt p 11 0 countB
  countTry : CodeAt p 12 0 countTryB
  boundedFix : CodeAt p 13 0 boundedFixB
  fixSelf : ∃ tb m, Pr p N (lamEnv fixBody) ((capt fixBody).length + 1) noOut fixBody tb m ∧
    m ≤ N ∧ CodeAt p fixSelfCode (capt fixBody).length
      (dropIf (!mentions fixBody 0) (capt fixBody).length tb)

theorem codeAt_of_rt {p : Prog} {s : PS} (hp : Ext p s) (hg : Grows rtPS s) {i k : Nat} {body : Tm}
    (hi : i < 14) (hf : rtPS.fns[i]? = some (lamFn k body))
    (hc : rtPS.codes[i]? = some (lamCode i)) : CodeAt p i k body := by
  have h1 := hp i (by have := hg.1; rw [rtPS_size.1] at this; omega)
  have h2 := hg.2.1 i (by rw [rtPS_size.1]; exact hi)
  exact ⟨by rw [h1.2, h2.2, hc], lamFn k body, by rw [h1.1, h2.1, hf], rfl, rfl⟩

theorem effFreeB_fixBody : effFreeB (.lam fixBody) = true := rfl

/-- **The primitives' codes are any program's that holds the prelude's tables.** -/
theorem rt_of_ext {p : Prog} {s : PS} {N : Nat} (hp : Ext p s) (hg : Grows preludePS s)
    (hN : s.bound ≤ N) : RT p N := by
  obtain ⟨h1, g1, p1⟩ := prG_pr (.lam fixBody) (fun _ => 0) 0 noOut rtPS effFreeB_fixBody
    (by rw [rtPS_size.1, rtPS_size.2.1])
  rw [← preludePS_eq] at h1 g1 p1
  have hg' : Grows rtPS s := g1.trans hg
  refine ⟨codeAt_of_rt hp hg' (by decide) rfl rfl, codeAt_of_rt hp hg' (by decide) rfl rfl,
    codeAt_of_rt hp hg' (by decide) rfl rfl, codeAt_of_rt hp hg' (by decide) rfl rfl,
    codeAt_of_rt hp hg' (by decide) rfl rfl, codeAt_of_rt hp hg' (by decide) rfl rfl,
    codeAt_of_rt hp hg' (by decide) rfl rfl, codeAt_of_rt hp hg' (by decide) rfl rfl,
    codeAt_of_rt hp hg' (by decide) rfl rfl, codeAt_of_rt hp hg' (by decide) rfl rfl,
    codeAt_of_rt hp hg' (by decide) rfl rfl, codeAt_of_rt hp hg' (by decide) rfl rfl,
    codeAt_of_rt hp hg' (by decide) rfl rfl, codeAt_of_rt hp hg' (by decide) rfl rfl, ?_⟩
  have hpr := p1 p N (hp.mono hg) (hg.2.2.trans hN)
  have hc : (prG (fun _ => 0) 0 noOut (.lam fixBody) rtPS).1.1 =
      envCopies (fun _ => 0) noOut (capt fixBody) 0
        (.clos fixSelfCode (envVars (fun _ => 0) noOut (capt fixBody) 0)) := rfl
  rw [hc] at hpr
  generalize hT : envCopies (fun _ => 0) noOut (capt fixBody) 0
    (.clos fixSelfCode (envVars (fun _ => 0) noOut (capt fixBody) 0)) = T at hpr
  cases hpr with
  | lam c hb hm hcode =>
      have hc14 : c = fixSelfCode := by
        simp only [capt, fixBody] at hT
        cases hT; rfl
      subst hc14
      exact ⟨_, _, hb, hm, hcode⟩

theorem tyTable_get (N : Nat) : ∀ x, x < N → (tyTable N)[x]? = some LTy.unit := by
  have key : ∀ (l : List Nat) (m : Std.HashMap Var LTy) x,
      (l.foldl (fun m x => m.insert x LTy.unit) m)[x]? = if x ∈ l then some LTy.unit else m[x]? := by
    intro l
    induction l with
    | nil => intro m x; simp
    | cons a l ih =>
        intro m x
        simp only [List.foldl_cons, ih, List.mem_cons, Std.HashMap.getElem?_insert]
        by_cases h : x ∈ l
        · simp [h]
        · by_cases ha : a = x
          · subst ha; simp
          · simp [h, ha, Ne.symm ha]
  intro x hx
  simp only [tyTable, key]
  simp [hx]

theorem preludePS_ok : preludePS.fns.size = preludePS.codes.size ∧ Grows rtPS preludePS := by
  obtain ⟨h1, g1, -⟩ := prG_pr (.lam fixBody) (fun _ => 0) 0 noOut rtPS effFreeB_fixBody
    (by rw [rtPS_size.1, rtPS_size.2.1])
  exact ⟨h1, g1⟩

/-- **The program of a closed effect-free term is its print**: `main` is a print of the term over
the program's codes, the primitives' codes are in it, and every variable below `N` is at
`unit`. -/
theorem lirOf_pr (e : Expr) (hc : effFreeB e = true) :
    ∃ N n', Pr (lirOf e) N (fun _ => 0) 0 noOut e (lirOf e).main n' ∧ n' ≤ N ∧ rtBound ≤ N ∧
      RT (lirOf e) N ∧ ∀ x, x < N → (lirOf e).ty[x]? = some LTy.unit := by
  obtain ⟨-, g, hp⟩ := prG_pr e (fun _ => 0) 0 noOut preludePS hc preludePS_ok.1
  have hext : Ext (lirOf e) (prG (fun _ => 0) 0 noOut e preludePS).2 := fun i _ => ⟨rfl, rfl⟩
  have hb : rtBound ≤ (prG (fun _ => 0) 0 noOut e preludePS).2.bound :=
    le_trans (by rw [rtPS_size.2.2]) (le_trans preludePS_ok.2.2.2 g.2.2)
  refine ⟨max (prG (fun _ => 0) 0 noOut e preludePS).2.bound (prG (fun _ => 0) 0 noOut e preludePS).1.2,
    (prG (fun _ => 0) 0 noOut e preludePS).1.2, hp _ _ hext (le_max_left _ _), le_max_right _ _,
    le_trans hb (le_max_left _ _), rt_of_ext hext g (le_max_left _ _), tyTable_get _⟩

end Lowering
