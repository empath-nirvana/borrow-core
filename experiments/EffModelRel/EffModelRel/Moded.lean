import EffModelRel.UnaryCompat

/-!
# EffModelRel — masks and rows for the moded judgement

Phase A's checks, on the intrinsic terms:

- a **mask** `L` says which linear variables a term consumes; every other variable is either not
  linear or belongs to the context (the grades of phase A, read for linear variables, the only
  ones that own anything);
- a **row** `R` says which instances a term may perform on. Its mode, the join of the bounds of
  their effects, is the bound phase A's `Ctx.bound` computes (`Row.mode`); a type's row (`Rw`,
  by level) is read as one by `Rw.vset`;
- a type is **scoped** under `n` instances (`VTy.Sc`) when its rows name only levels below `n`:
  an instance never appears in a type outside its binder (`docs/effects-tr` §2, *scope*).
-/

namespace EffRel

variable {S : Sig}

/-- A set of variables of a context. -/
abbrev VSet {α : Type} (Γ : List α) : Type := (a : α) → Var Γ a → Bool

namespace VSet
variable {α : Type} {Γ : List α}
def none : VSet Γ := fun _ _ => false
def cons {a : α} (b : Bool) (L : VSet Γ) : VSet (a :: Γ)
  | _, .z => b
  | _, .s x => L _ x
def tail {a : α} (L : VSet (a :: Γ)) : VSet Γ := fun b x => L b (.s x)
def union (L₁ L₂ : VSet Γ) : VSet Γ := fun a x => L₁ a x || L₂ a x
def Disj (L₁ L₂ : VSet Γ) : Prop := ∀ a x, L₁ a x = true → L₂ a x = false
def Empty (L : VSet Γ) : Prop := ∀ a x, L a x = false
def Sub (L₁ L₂ : VSet Γ) : Prop := ∀ a x, L₁ a x = true → L₂ a x = true
def single : {Γ : List α} → {a : α} → Var Γ a → VSet Γ
  | _ :: _, _, .z => cons true none
  | _ :: _, _, .s x => cons false (single x)

@[simp] theorem cons_z {a : α} (b : Bool) (L : VSet Γ) : (cons (a := a) b L) a .z = b := rfl
@[simp] theorem cons_s {a c : α} (b : Bool) (L : VSet Γ) (x : Var Γ c) :
    (cons (a := a) b L) c (.s x) = L c x := rfl
@[simp] theorem tail_cons {a : α} (b : Bool) (L : VSet Γ) : (cons (a := a) b L).tail = L := rfl
@[simp] theorem none_apply (a : α) (x : Var Γ a) : (none : VSet Γ) a x = false := rfl
@[simp] theorem union_apply (L₁ L₂ : VSet Γ) (a : α) (x : Var Γ a) :
    (L₁.union L₂) a x = (L₁ a x || L₂ a x) := rfl
theorem tail_union {a : α} (L₁ L₂ : VSet (a :: Γ)) : (L₁.union L₂).tail = L₁.tail.union L₂.tail := rfl
theorem tail_none {a : α} : (none : VSet (a :: Γ)).tail = none := rfl

theorem Disj.tail {a : α} {L₁ L₂ : VSet (a :: Γ)} (h : Disj L₁ L₂) : Disj L₁.tail L₂.tail :=
  fun b x => h b (.s x)

theorem Empty.tail {a : α} {L : VSet (a :: Γ)} (h : Empty L) : Empty L.tail := fun b x => h b (.s x)
end VSet

/-! ## Ownership of the variables a term consumes -/

/-- The tokens owned by the variables of `L`. -/
def sumL : (Γ : List (VTy S)) → VSet Γ → ((A : VTy S) → Var Γ A → Own) → Own
  | [], _, _ => 0
  | A :: Γ, L, Os => (if L A .z then Os A .z else 0) + sumL Γ L.tail (fun B x => Os B (.s x))

theorem sumL_none : (Γ : List (VTy S)) → ∀ (Os : (A : VTy S) → Var Γ A → Own),
    sumL Γ VSet.none Os = 0
  | [], _ => rfl
  | _ :: Γ, Os => by simp only [sumL, VSet.none_apply]; rw [VSet.tail_none, sumL_none Γ]; rfl

theorem sumL_empty {Γ : List (VTy S)} {L : VSet Γ} (h : L.Empty) (Os) : sumL Γ L Os = 0 := by
  have : L = VSet.none := funext fun a => funext fun x => h a x
  subst this; exact sumL_none Γ Os

theorem sumL_union : (Γ : List (VTy S)) → ∀ {L₁ L₂ : VSet Γ} (Os : (A : VTy S) → Var Γ A → Own),
    L₁.Disj L₂ → sumL Γ (L₁.union L₂) Os = sumL Γ L₁ Os + sumL Γ L₂ Os
  | [], _, _, _, _ => by simp [sumL]
  | A :: Γ, L₁, L₂, Os, hd => by
      simp only [sumL, VSet.union_apply]
      rw [VSet.tail_union, sumL_union Γ _ hd.tail]
      have h0 := hd A .z
      apply Own.ext; intro k n
      by_cases h1 : L₁ A .z = true
      · have h2 := h0 h1; simp [h1, h2]; omega
      · have h1' : L₁ A .z = false := by simpa using h1
        by_cases h2 : L₂ A .z = true
        · simp [h1', h2]; omega
        · have h2' : L₂ A .z = false := by simpa using h2
          simp [h1', h2']

theorem sumL_cons {A : VTy S} {Γ : List (VTy S)} (b : Bool) (L : VSet Γ)
    (Os : (B : VTy S) → Var (A :: Γ) B → Own) :
    sumL (A :: Γ) (VSet.cons b L) Os = (if b then Os A .z else 0) + sumL Γ L (fun B x => Os B (.s x)) :=
  rfl

theorem sumL_single : {Γ : List (VTy S)} → {A : VTy S} → (x : Var Γ A) →
    ∀ (Os : (B : VTy S) → Var Γ B → Own), sumL Γ (VSet.single x) Os = Os A x
  | _ :: Γ, _, .z, Os => by
      simp only [VSet.single, sumL_cons, if_true]; rw [sumL_none]; simp
  | _ :: Γ, _, .s x, Os => by
      simp only [VSet.single, sumL_cons, Bool.false_eq_true, if_false, Own.zero_add]
      exact sumL_single x _

/-! ## Rows -/

structure Row (S : Sig) (Ψ : List S.E) where
  v : VSet Ψ

namespace Row
variable {Ψ : List S.E}
def none : Row S Ψ := ⟨VSet.none⟩
def union (R₁ R₂ : Row S Ψ) : Row S Ψ := ⟨R₁.v.union R₂.v⟩
def inst {e : S.E} (x : Var Ψ e) : Row S Ψ := ⟨VSet.single x⟩
def tail {e : S.E} (R : Row S (e :: Ψ)) : Row S Ψ := ⟨R.v.tail⟩
def Sub (R₁ R₂ : Row S Ψ) : Prop := R₁.v.Sub R₂.v
end Row

def IEnv.tail {e : S.E} (η : IEnv (S := S) (e :: Ψ)) : IEnv Ψ := fun e' x => η e' (.s x)

theorem IEnv.tail_cons {e : S.E} (i : Nat) (η : IEnv (S := S) Ψ) : (η.cons (e := e) i).tail = η := rfl

/-- Whether an instance variable of the set names instance `j` of effect `e`. -/
def hits : (Ψ : List S.E) → IEnv Ψ → VSet Ψ → Nat → S.E → Bool
  | [], _, _, _, _ => false
  | e₀ :: Ψ, η, v, j, e =>
      (decide (e₀ = e) && v e₀ .z && decide (η e₀ .z = j)) || hits Ψ η.tail v.tail j e

/-- The permissions of a row in an instance environment. -/
def okOf (η : IEnv Ψ) (R : Row S Ψ) : Ok S := fun j e => hits Ψ η R.v j e = true

/-- The static bound of a set of instance variables. -/
def rowMode : (Ψ : List S.E) → VSet Ψ → Mode
  | [], _ => Mode.lin
  | e₀ :: Ψ, v => (if v e₀ .z then S.bnd e₀ else Mode.lin).join (rowMode Ψ v.tail)

/-- The mode of a row: the join of its effects' bounds, phase A's `Bound.req` of it. -/
def Row.mode {Ψ : List S.E} (R : Row S Ψ) : Mode := rowMode Ψ R.v

/-! ## Levels -/

/-- The level of an instance variable: its position from the outermost end of the context. -/
def Var.lvl {α : Type} : {Γ : List α} → {a : α} → Var Γ a → Nat
  | _ :: Γ, _, .z => Γ.length
  | _ :: _, _, .s x => x.lvl

theorem Var.lvl_lt {α : Type} : {Γ : List α} → {a : α} → (x : Var Γ a) → x.lvl < Γ.length
  | _ :: _, _, .z => by simp [Var.lvl]
  | _ :: _, _, .s x => by simp only [Var.lvl, List.length_cons]; have := x.lvl_lt; omega

/-- The instances of an environment by level, with their effects. -/
def IEnv.lv : {Ψ : List S.E} → IEnv Ψ → LEnv S
  | [], _ => []
  | e :: _, η => η.tail.lv ++ [(η e .z, e)]

@[simp] theorem IEnv.lv_cons {e : S.E} (i : Nat) (η : IEnv (S := S) Ψ) :
    (η.cons (e := e) i).lv = η.lv ++ [(i, e)] := rfl

theorem IEnv.lv_length : {Ψ : List S.E} → (η : IEnv (S := S) Ψ) → η.lv.length = Ψ.length
  | [], _ => rfl
  | _ :: _, η => by simp [IEnv.lv, IEnv.lv_length η.tail]

/-- Level `n` of an environment is the instance of the variable at that level. -/
theorem IEnv.lv_get : {Ψ : List S.E} → (η : IEnv (S := S) Ψ) → (n : Nat) → (i : Nat) → (e : S.E) →
    (η.lv[n]? = some (i, e) ↔ ∃ x : Var Ψ e, x.lvl = n ∧ η e x = i)
  | [], _, n, i, e => by simp [IEnv.lv]; intro x; exact nomatch x
  | e₀ :: Ψ, η, n, i, e => by
      simp only [IEnv.lv]
      by_cases hn : n < Ψ.length
      · rw [List.getElem?_append_left (by rw [IEnv.lv_length]; exact hn), IEnv.lv_get η.tail n i e]
        constructor
        · rintro ⟨x, hx, rfl⟩; exact ⟨.s x, hx, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          cases x with
          | z => simp [Var.lvl] at hx; omega
          | s x => exact ⟨x, hx, rfl⟩
      · rw [List.getElem?_append_right (by rw [IEnv.lv_length]; omega), IEnv.lv_length]
        by_cases hn' : n = Ψ.length
        · subst hn'
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq]
          constructor
          · rintro ⟨rfl, rfl⟩; exact ⟨.z, rfl, rfl⟩
          · rintro ⟨x, hx, rfl⟩
            cases x with
            | z => exact ⟨rfl, rfl⟩
            | s x => have := x.lvl_lt; simp [Var.lvl] at hx; omega
        · have : n - Ψ.length ≠ 0 := by omega
          simp only [List.getElem?_cons, this, if_false, List.getElem?_nil]
          constructor
          · intro h; cases h
          · rintro ⟨x, hx, rfl⟩
            cases x with
            | z => simp [Var.lvl] at hx; omega
            | s x => have := x.lvl_lt; simp [Var.lvl] at hx; omega

theorem hits_iff : (Ψ : List S.E) → (η : IEnv Ψ) → (v : VSet Ψ) → (j : Nat) → (e : S.E) →
    (hits Ψ η v j e = true ↔ ∃ x : Var Ψ e, v e x = true ∧ η e x = j)
  | [], _, _, _, _ => by simp [hits]; intro x; exact nomatch x
  | e₀ :: Ψ, η, v, j, e => by
      simp only [hits, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, hits_iff Ψ]
      constructor
      · rintro (⟨⟨rfl, h⟩, rfl⟩ | ⟨x, hx, rfl⟩)
        · exact ⟨.z, h, rfl⟩
        · exact ⟨.s x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        cases x with
        | z => exact .inl ⟨⟨rfl, hx⟩, rfl⟩
        | s x => exact .inr ⟨x, hx, rfl⟩

/-- A type's row as a set of instance variables. -/
def Rw.vset (Ψ : List S.E) (ρ : Rw) : VSet Ψ := fun _ x => ρ.insts.contains x.lvl

def Rw.row (Ψ : List S.E) (ρ : Rw) : Row S Ψ := ⟨ρ.vset Ψ⟩

/-- **A type's row and its set of variables give the same permissions.** -/
theorem okOf_row (η : IEnv Ψ) (ρ : Rw) : okOf η (ρ.row Ψ) = ρ.ok η.lv := by
  funext j e
  apply propext
  simp only [okOf, Rw.row, hits_iff, Rw.vset, Rw.ok, List.contains_iff_mem, Rw.insts,
    List.mem_map]
  constructor
  · rintro ⟨x, ⟨p, hp, hpx⟩, rfl⟩
    exact ⟨p, hp, by rw [hpx]; exact (IEnv.lv_get η _ _ _).2 ⟨x, rfl, rfl⟩⟩
  · rintro ⟨p, hp, hg⟩
    obtain ⟨x, hx, rfl⟩ := (IEnv.lv_get η _ _ _).1 hg
    exact ⟨x, ⟨p, hp, hx.symm⟩, rfl⟩

/-! ## Scope -/

mutual
/-- A type mentions only the first `n` levels. -/
def VTy.Sc (n : Nat) : VTy S → Prop
  | .g _ => True
  | .prod A B => A.Sc n ∧ B.Sc n
  | .sum A B => A.Sc n ∧ B.Sc n
  | .U _ b C => b.Sc n ∧ C.Sc n
  | .cap _ _ => True
  | .strm b A => b.Sc n ∧ A.Sc n
def CTy.Sc (n : Nat) : CTy S → Prop
  | .F A => A.Sc n
  | .arr A b C => A.Sc n ∧ b.Sc n ∧ C.Sc n
  | .wth C D => C.Sc n ∧ D.Sc n
  | .pi _ C => C.Sc n
end

theorem Rw.Sc.mono {n m : Nat} (h : n ≤ m) {ρ : Rw} (hρ : ρ.Sc n) : ρ.Sc m :=
  fun p hp => ⟨by have := (hρ p hp).1; omega, by have := (hρ p hp).2; omega⟩

mutual
theorem VTy.Sc.mono {n m : Nat} (h : n ≤ m) : (A : VTy S) → A.Sc n → A.Sc m
  | .g _, _ => trivial
  | .prod A B, hA => ⟨VTy.Sc.mono h A hA.1, VTy.Sc.mono h B hA.2⟩
  | .sum A B, hA => ⟨VTy.Sc.mono h A hA.1, VTy.Sc.mono h B hA.2⟩
  | .U _ _ C, hA => ⟨Rw.Sc.mono h hA.1, CTy.Sc.mono h C hA.2⟩
  | .cap _ _, _ => trivial
  | .strm _ A, hA => ⟨Rw.Sc.mono h hA.1, VTy.Sc.mono h A hA.2⟩
theorem CTy.Sc.mono {n m : Nat} (h : n ≤ m) : (C : CTy S) → C.Sc n → C.Sc m
  | .F A, hC => VTy.Sc.mono h A hC
  | .arr A _ C, hC => ⟨VTy.Sc.mono h A hC.1, Rw.Sc.mono h hC.2.1, CTy.Sc.mono h C hC.2.2⟩
  | .wth C D, hC => ⟨CTy.Sc.mono h C hC.1, CTy.Sc.mono h D hC.2⟩
  | .pi _ C, hC => CTy.Sc.mono h C hC
end

/-- A row's permissions do not see an instance beyond its scope. -/
theorem Rw.ok_ext {θ : LEnv S} {ρ : Rw} (hρ : ρ.Sc θ.length) (p : Nat × S.E) :
    ρ.ok (θ ++ [p]) = ρ.ok θ := by
  funext i e
  apply propext
  simp only [Rw.ok]
  constructor
  · rintro ⟨q, hq, hg⟩
    exact ⟨q, hq, by rwa [List.getElem?_append_left (hρ q hq).1] at hg⟩
  · rintro ⟨q, hq, hg⟩
    exact ⟨q, hq, by rwa [List.getElem?_append_left (hρ q hq).1]⟩

/-! ## Facts about modes and rows -/

namespace Mode
theorem ge_join_l (a b : Mode) : (a.join b).ge a = true := by
  obtain ⟨aw, ac⟩ := a; obtain ⟨bw, bc⟩ := b
  cases aw <;> cases ac <;> cases bw <;> cases bc <;> rfl
theorem ge_join_r (a b : Mode) : (a.join b).ge b = true := by
  obtain ⟨aw, ac⟩ := a; obtain ⟨bw, bc⟩ := b
  cases aw <;> cases ac <;> cases bw <;> cases bc <;> rfl
theorem join_ge {a b c : Mode} (h₁ : c.ge a = true) (h₂ : c.ge b = true) : c.ge (a.join b) = true := by
  obtain ⟨aw, ac⟩ := a; obtain ⟨bw, bc⟩ := b; obtain ⟨cw, cc⟩ := c
  cases aw <;> cases ac <;> cases bw <;> cases bc <;> cases cw <;> cases cc <;> simp_all [ge, join]
theorem ge_lin (a : Mode) : a.ge Mode.lin = true := by
  obtain ⟨aw, ac⟩ := a; cases aw <;> cases ac <;> rfl
theorem lin_join (a : Mode) : Mode.lin.join a = a := by
  obtain ⟨aw, ac⟩ := a; cases aw <;> cases ac <;> rfl
theorem ge_refl (a : Mode) : a.ge a = true := by
  obtain ⟨aw, ac⟩ := a; cases aw <;> cases ac <;> rfl
theorem isLin_lin : Mode.lin.IsLin := ⟨rfl, rfl⟩
theorem isLin_of_ge {a b : Mode} (ha : a.IsLin) (h : a.ge b = true) : b.IsLin :=
  isLin_of_ge_lin ha h
end Mode

theorem hits_mono : (Ψ : List S.E) → ∀ (η : IEnv Ψ) {v₁ v₂ : VSet Ψ} (j : Nat) (e : S.E),
    v₁.Sub v₂ → hits Ψ η v₁ j e = true → hits Ψ η v₂ j e = true := by
  intro Ψ η v₁ v₂ j e hs h
  rw [hits_iff] at h ⊢
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x, hs _ _ hx, rfl⟩

theorem rowMode_ge : (Ψ : List S.E) → ∀ (η : IEnv Ψ) (v : VSet Ψ) (j : Nat) (e : S.E),
    hits Ψ η v j e = true → (rowMode Ψ v).ge (S.bnd e) = true
  | [], _, _, _, _, h => by simp [hits] at h
  | e₀ :: Ψ, η, v, j, e, h => by
      simp only [hits, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [rowMode]
      rcases h with ⟨⟨rfl, h2⟩, _⟩ | h
      · rw [if_pos h2]; exact Mode.ge_join_l _ _
      · exact Mode.ge_trans (Mode.ge_join_r _ _) (rowMode_ge Ψ η.tail v.tail j e h)

/-- A row whose mode is linear permits only linear effects. -/
theorem Row.isLin_ok {Ψ : List S.E} {R : Row S Ψ} (h : R.mode.IsLin) (η : IEnv Ψ) :
    (okOf η R).IsLin := fun j e hj => Mode.isLin_of_ge h (rowMode_ge Ψ η R.v j e hj)

theorem Row.noC_ok {Ψ : List S.E} {R : Row S Ψ} (h : R.mode.c = false) (η : IEnv Ψ) :
    (okOf η R).NoC := fun j e hj => by
  have := rowMode_ge Ψ η R.v j e hj
  revert this h; unfold Row.mode; generalize rowMode Ψ R.v = m
  obtain ⟨w, c⟩ := m; obtain ⟨w', c'⟩ := S.bnd e
  cases c <;> cases c' <;> cases w <;> cases w' <;> simp [Mode.ge]

theorem okOf_sub {Ψ : List S.E} {R₁ R₂ : Row S Ψ} (h : R₁.Sub R₂) (η : IEnv Ψ) :
    (okOf η R₁).le (okOf η R₂) := fun j e hj => hits_mono Ψ η j e h hj

theorem Row.sub_union_l {Ψ : List S.E} (R₁ R₂ : Row S Ψ) : R₁.Sub (R₁.union R₂) :=
  fun a x h => by simp [Row.union, h]
theorem Row.sub_union_r {Ψ : List S.E} (R₁ R₂ : Row S Ψ) : R₂.Sub (R₁.union R₂) :=
  fun a x h => by simp [Row.union, h]
theorem Row.sub_refl {Ψ : List S.E} (R : Row S Ψ) : R.Sub R := fun _ _ h => h
theorem Row.sub_trans {Ψ : List S.E} {R₁ R₂ R₃ : Row S Ψ} (h₁ : R₁.Sub R₂) (h₂ : R₂.Sub R₃) :
    R₁.Sub R₃ := fun a x h => h₂ a x (h₁ a x h)
theorem Row.union_sub {Ψ : List S.E} {R₁ R₂ R₃ : Row S Ψ} (h₁ : R₁.Sub R₃) (h₂ : R₂.Sub R₃) :
    (R₁.union R₂).Sub R₃ := fun a x h => by
  simp only [Row.union, VSet.union_apply, Bool.or_eq_true] at h
  exact h.elim (h₁ a x) (h₂ a x)

theorem okOf_union {Ψ : List S.E} (η : IEnv Ψ) (R₁ R₂ : Row S Ψ) :
    (okOf η (R₁.union R₂)).le ((okOf η R₁).union (okOf η R₂)) := fun j e h => by
  simp only [okOf, hits_iff, Row.union, VSet.union_apply, Bool.or_eq_true] at h
  obtain ⟨x, hx | hx, rfl⟩ := h
  · exact .inl ((hits_iff Ψ η _ _ _).2 ⟨x, hx, rfl⟩)
  · exact .inr ((hits_iff Ψ η _ _ _).2 ⟨x, hx, rfl⟩)

theorem okOf_union' {Ψ : List S.E} (η : IEnv Ψ) (R₁ R₂ : Row S Ψ) :
    ((okOf η R₁).union (okOf η R₂)).le (okOf η (R₁.union R₂)) :=
  Ok.union_le (okOf_sub (Row.sub_union_l _ _) η) (okOf_sub (Row.sub_union_r _ _) η)

theorem okOf_none {Ψ : List S.E} (η : IEnv Ψ) : okOf η (Row.none (S := S)) = Ok.bot := by
  funext j e; apply propext
  simp only [okOf, hits_iff, Row.none, VSet.none_apply, Ok.bot]
  constructor
  · rintro ⟨_, h, _⟩; cases h
  · intro h; exact h.elim

theorem okOf_inst {Ψ : List S.E} {e : S.E} (η : IEnv Ψ) (x : Var Ψ e) : okOf η (Row.inst x) (η e x) e :=
  (hits_iff Ψ η _ _ _).2 ⟨x, by
    induction x with
    | z => simp [Row.inst, VSet.single]
    | s x ih => simpa [Row.inst, VSet.single] using ih, rfl⟩

/-- Under an instance binder: the row's permissions are its tail's, and the new instance. -/
theorem okOf_cons {Ψ : List S.E} {e₀ : S.E} (R : Row S (e₀ :: Ψ)) (η : IEnv Ψ) (i : Nat) :
    (okOf (η.cons i) R).le ((okOf η R.tail).add i e₀) := fun j e h => by
  simp only [okOf, hits, IEnv.tail_cons, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨rfl, _⟩, rfl⟩ | h
  · exact .inr ⟨rfl, rfl⟩
  · exact .inl h

theorem okOf_cons_rem {Ψ : List S.E} {e₀ : S.E} (R : Row S (e₀ :: Ψ)) (η : IEnv Ψ) (i : Nat) :
    ((okOf (η.cons i) R).rem i e₀).le (okOf η R.tail) := fun j e h =>
  ((okOf_cons R η i j e h.1).resolve_right h.2)

theorem okOf_cons_tail {Ψ : List S.E} {e₀ : S.E} (R : Row S (e₀ :: Ψ)) (η : IEnv Ψ) (i : Nat)
    (hz : R.v e₀ .z = false) : (okOf (η.cons i) R).le (okOf η R.tail) := fun j e h => by
  simp only [okOf, hits, IEnv.tail_cons, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨rfl, hz'⟩, _⟩ | h
  · rw [hz] at hz'; cases hz'
  · exact h

theorem Row.tail_mode_ge {Ψ : List S.E} {e₀ : S.E} (R : Row S (e₀ :: Ψ)) :
    R.mode.ge R.tail.mode = true := by
  simp only [Row.mode, rowMode, Row.tail]; exact Mode.ge_join_r _ _

theorem Row.isLin_tail {Ψ : List S.E} {e₀ : S.E} {R : Row S (e₀ :: Ψ)} (η : IEnv Ψ) (i : Nat)
    (h : R.tail.mode.IsLin) :
    ∀ j e, ¬ (j = i ∧ e = e₀) → okOf (η.cons i) R j e → (S.bnd e).IsLin := fun j e hne hj =>
  Row.isLin_ok h η j e ((okOf_cons R η i j e hj).resolve_right hne)

end EffRel
