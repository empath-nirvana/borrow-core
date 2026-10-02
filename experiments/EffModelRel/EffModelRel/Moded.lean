import EffModelRel.UnaryCompat

/-!
# EffModelRel — masks and rows for the moded judgement

Phase A's checks, on the intrinsic terms:

- a **mask** `L` says which linear variables a term consumes; every other variable is either not
  linear or belongs to the context (the grades of phase A, read for linear variables, the only
  ones that own anything);
- a **row** `R` says which instances a term may perform on, and the bound of the operations of
  the thunks and functions it runs (`fb`). Its mode is the bound phase A's `Ctx.bound` computes.
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
  fb : Mode

namespace Row
variable {Ψ : List S.E}
def none : Row S Ψ := ⟨VSet.none, Mode.lin⟩
def union (R₁ R₂ : Row S Ψ) : Row S Ψ := ⟨R₁.v.union R₂.v, R₁.fb.join R₂.fb⟩
def inst {e : S.E} (x : Var Ψ e) : Row S Ψ := ⟨VSet.single x, Mode.lin⟩
def fgn (m : Mode) : Row S Ψ := ⟨VSet.none, m⟩
def tail {e : S.E} (R : Row S (e :: Ψ)) : Row S Ψ := ⟨R.v.tail, R.fb⟩
/-- Remove an instance variable. -/
def erase {e : S.E} (R : Row S Ψ) (x : Var Ψ e) : Row S Ψ :=
  ⟨fun e' y => R.v e' y && !(VSet.single x e' y), R.fb⟩
def Sub (R₁ R₂ : Row S Ψ) : Prop := R₁.v.Sub R₂.v ∧ R₂.fb.ge R₁.fb = true
end Row

def IEnv.tail {e : S.E} (η : IEnv (S := S) (e :: Ψ)) : IEnv Ψ := fun e' x => η e' (.s x)

/-- Whether an instance variable of the set names instance `j` of effect `e`. -/
def hits : (Ψ : List S.E) → IEnv Ψ → VSet Ψ → Nat → S.E → Bool
  | [], _, _, _, _ => false
  | e₀ :: Ψ, η, v, j, e =>
      (decide (e₀ = e) && v e₀ .z && decide (η e₀ .z = j)) || hits Ψ η.tail v.tail j e

/-- The semantic bound of a row in an instance environment. -/
def bndOf (η : IEnv Ψ) (R : Row S Ψ) : Bnd S :=
  fun j e => (if hits Ψ η R.v j e then S.bnd e else Mode.lin).join R.fb

/-- The static bound of a set of instance variables. -/
def rowMode : (Ψ : List S.E) → VSet Ψ → Mode
  | [], _ => Mode.lin
  | e₀ :: Ψ, v => (if v e₀ .z then S.bnd e₀ else Mode.lin).join (rowMode Ψ v.tail)

/-- The mode of a row: phase A's `Bound.req` of it. -/
def Row.mode {Ψ : List S.E} (R : Row S Ψ) : Mode := (rowMode Ψ R.v).join R.fb

/-! ## Facts about modes, bounds and rows -/

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
theorem join_mono {a b c d : Mode} (h₁ : c.ge a = true) (h₂ : d.ge b = true) :
    (c.join d).ge (a.join b) = true :=
  join_ge (ge_trans (ge_join_l c d) h₁) (ge_trans (ge_join_r c d) h₂)
theorem ge_refl (a : Mode) : a.ge a = true := by
  obtain ⟨aw, ac⟩ := a; cases aw <;> cases ac <;> rfl
theorem isLin_lin : Mode.lin.IsLin := ⟨rfl, rfl⟩
theorem isLin_of_ge {a b : Mode} (ha : a.IsLin) (h : a.ge b = true) : b.IsLin :=
  isLin_of_ge_lin ha h
end Mode

theorem hits_mono : (Ψ : List S.E) → ∀ (η : IEnv Ψ) {v₁ v₂ : VSet Ψ} (j : Nat) (e : S.E),
    v₁.Sub v₂ → hits Ψ η v₁ j e = true → hits Ψ η v₂ j e = true
  | [], _, _, _, _, _, _, h => by simp [hits] at h
  | e₀ :: Ψ, η, v₁, v₂, j, e, hs, h => by
      simp only [hits, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      rcases h with ⟨⟨h1, h2⟩, h3⟩ | h
      · exact .inl ⟨⟨h1, hs _ _ h2⟩, h3⟩
      · exact .inr (hits_mono Ψ η.tail j e (fun a x => hs a (.s x)) h)

theorem rowMode_ge : (Ψ : List S.E) → ∀ (η : IEnv Ψ) (v : VSet Ψ) (j : Nat) (e : S.E),
    hits Ψ η v j e = true → (rowMode Ψ v).ge (S.bnd e) = true
  | [], _, _, _, _, h => by simp [hits] at h
  | e₀ :: Ψ, η, v, j, e, h => by
      simp only [hits, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [rowMode]
      rcases h with ⟨⟨rfl, h2⟩, _⟩ | h
      · rw [if_pos h2]; exact Mode.ge_join_l _ _
      · exact Mode.ge_trans (Mode.ge_join_r _ _) (rowMode_ge Ψ η.tail v.tail j e h)

theorem Row.mode_ge {Ψ : List S.E} (R : Row S Ψ) (η : IEnv Ψ) (j : Nat) (e : S.E) :
    R.mode.ge (bndOf η R j e) = true := by
  unfold bndOf Row.mode
  apply Mode.join_mono _ (Mode.ge_refl _)
  split
  · exact rowMode_ge Ψ η R.v j e (by assumption)
  · exact Mode.ge_lin _

/-- A row whose mode is linear bounds only linear operations. -/
theorem Row.isLin_bnd {Ψ : List S.E} {R : Row S Ψ} (h : R.mode.IsLin) (η : IEnv Ψ) :
    (bndOf η R).IsLin := fun j e => Mode.isLin_of_ge h (R.mode_ge η j e)

theorem bndOf_sub {Ψ : List S.E} {R₁ R₂ : Row S Ψ} (h : R₁.Sub R₂) (η : IEnv Ψ) :
    (bndOf η R₁).le (bndOf η R₂) := fun j e => by
  unfold bndOf
  apply Mode.join_mono _ h.2
  by_cases h1 : hits Ψ η R₁.v j e = true
  · rw [if_pos h1, if_pos (hits_mono Ψ η j e h.1 h1)]; exact Mode.ge_refl _
  · rw [if_neg h1]; exact Mode.ge_lin _

theorem Row.sub_union_l {Ψ : List S.E} (R₁ R₂ : Row S Ψ) : R₁.Sub (R₁.union R₂) :=
  ⟨fun a x h => by simp [Row.union, h], Mode.ge_join_l _ _⟩
theorem Row.sub_union_r {Ψ : List S.E} (R₁ R₂ : Row S Ψ) : R₂.Sub (R₁.union R₂) :=
  ⟨fun a x h => by simp [Row.union, h], Mode.ge_join_r _ _⟩
theorem Row.sub_refl {Ψ : List S.E} (R : Row S Ψ) : R.Sub R := ⟨fun _ _ h => h, Mode.ge_refl _⟩
theorem Row.sub_trans {Ψ : List S.E} {R₁ R₂ R₃ : Row S Ψ} (h₁ : R₁.Sub R₂) (h₂ : R₂.Sub R₃) :
    R₁.Sub R₃ := ⟨fun a x h => h₂.1 a x (h₁.1 a x h), Mode.ge_trans h₂.2 h₁.2⟩
theorem Row.none_sub {Ψ : List S.E} (R : Row S Ψ) : (Row.none).Sub R :=
  ⟨fun _ _ h => by simp [Row.none] at h, Mode.ge_lin _⟩

theorem hits_single : (Ψ : List S.E) → ∀ {e : S.E} (η : IEnv Ψ) (x : Var Ψ e),
    hits Ψ η (VSet.single x) (η e x) e = true
  | _ :: _, _, _, .z => by simp [hits, VSet.single]
  | _ :: Ψ, _, η, .s x => by
      simp only [hits, VSet.single, VSet.cons_z, Bool.and_false, Bool.false_and, Bool.false_or,
        VSet.tail_cons]
      exact hits_single Ψ η.tail x

theorem bndOf_inst {Ψ : List S.E} {e : S.E} (η : IEnv Ψ) (x : Var Ψ e) :
    (bndOf η (Row.inst x) (η e x) e).ge (S.bnd e) = true := by
  simp only [bndOf, Row.inst, hits_single, if_true]; exact Mode.ge_join_l _ _

theorem hits_none : (Ψ : List S.E) → ∀ (η : IEnv Ψ) (j : Nat) (e : S.E),
    hits Ψ η VSet.none j e = false
  | [], _, _, _ => rfl
  | _ :: Ψ, η, j, e => by simp [hits, VSet.none_apply]; exact hits_none Ψ η.tail j e

theorem bndOf_fgn {Ψ : List S.E} (η : IEnv Ψ) (m : Mode) : bndOf η (Row.fgn m) = Bnd.const m := by
  funext j e; simp [bndOf, Row.fgn, hits_none, Bnd.const, Mode.lin_join]

theorem bndOf_none {Ψ : List S.E} (η : IEnv Ψ) : bndOf η (Row.none (S := S)) = Bnd.const Mode.lin :=
  bndOf_fgn η Mode.lin

theorem IEnv.tail_cons {e : S.E} (i : Nat) (η : IEnv (S := S) Ψ) : (η.cons (e := e) i).tail = η := rfl

/-- Under an instance binder: away from the new name, the row is its tail. -/
theorem bndOf_cons {Ψ : List S.E} {e₀ : S.E} (R : Row S (e₀ :: Ψ)) (η : IEnv Ψ) (i j : Nat)
    (e : S.E) (h : ¬ (j = i ∧ e = e₀) ∨ R.v e₀ .z = false) :
    bndOf (η.cons i) R j e = bndOf η R.tail j e := by
  unfold bndOf
  congr 1
  have : hits (e₀ :: Ψ) (η.cons i) R.v j e = hits Ψ η R.tail.v j e := by
    simp only [hits, IEnv.tail_cons, Row.tail]
    rcases h with h | h
    · have : (decide (e₀ = e) && R.v e₀ .z && decide ((η.cons i) e₀ .z = j)) = false := by
        simp only [IEnv.cons_z, Bool.and_eq_false_iff, decide_eq_false_iff_not]
        by_cases he : e₀ = e
        · subst he; exact .inr (decide_eq_false (fun hj => h ⟨hj.symm, rfl⟩))
        · exact .inl (.inl he)
      rw [this, Bool.false_or]
    · simp [h]
  rw [this]

theorem bndOf_ge_hits {Ψ : List S.E} {R : Row S Ψ} {η : IEnv Ψ} {j : Nat} {e : S.E}
    (h : hits Ψ η R.v j e = true) : (bndOf η R j e).ge (S.bnd e) = true := by
  unfold bndOf; rw [if_pos h]; exact Mode.ge_join_l _ _

theorem bndOf_ge_fb {Ψ : List S.E} (R : Row S Ψ) (η : IEnv Ψ) (j : Nat) (e : S.E) :
    (bndOf η R j e).ge R.fb = true := by
  unfold bndOf; exact Mode.ge_join_r _ _

theorem bndOf_cons_le {Ψ : List S.E} {e₀ : S.E} (R : Row S (e₀ :: Ψ)) (η : IEnv Ψ) (i : Nat) :
    (bndOf (η.cons i) R).le (bndOf η (R.tail.union (Row.fgn (if R.v e₀ .z then S.bnd e₀ else Mode.lin)))) :=
  fun j e => by
    by_cases h : j = i ∧ e = e₀
    · obtain ⟨rfl, rfl⟩ := h
      generalize hm : (if R.v e .z then S.bnd e else Mode.lin) = m
      have hfb : (bndOf η (R.tail.union (Row.fgn m)) j e).ge (R.fb.join m) = true :=
        bndOf_ge_fb (R.tail.union (Row.fgn m)) η j e
      have hl : bndOf (η.cons j) R j e =
          (if hits (e :: Ψ) (η.cons j) R.v j e then S.bnd e else Mode.lin).join R.fb := rfl
      rw [hl]
      apply Mode.join_ge _ (Mode.ge_trans hfb (Mode.ge_join_l _ _))
      by_cases hH : hits (e :: Ψ) (η.cons j) R.v j e = true
      · rw [if_pos hH]
        simp only [hits, IEnv.cons_z, decide_true, Bool.true_and, IEnv.tail_cons,
          Bool.or_eq_true, Bool.and_eq_true] at hH
        rcases hH with hz | ht
        · have hz' : R.v e .z = true := hz.1
          rw [if_pos hz'] at hm; subst hm
          exact Mode.ge_trans hfb (Mode.ge_join_r _ _)
        · exact bndOf_ge_hits (R := R.tail.union (Row.fgn m)) (hits_mono Ψ η j e
            (fun a x h => by simp [Row.union, Row.tail, Row.fgn, h]) ht)
      · rw [if_neg hH]; exact Mode.ge_lin _
    · rw [bndOf_cons R η i j e (.inl h)]
      exact bndOf_sub (Row.sub_union_l _ _) η j e

end EffRel
