import FrameTheorems

/-!
# TwoRun — renaming the locations of a run

`Expr.rename σ` replaces every location `ℓ` of a term by `σ ℓ`; `Heap.rename σ` moves the cell at
`ℓ` to `σ ℓ` and renames the value it holds.  For a permutation `σ` of `Loc`, every head step,
every step and every run is carried to a head step, step and run of the renamed configuration
(`head_rename`, `step1_rename`, `steps_rename`).

Away from the array steps, the machine names locations only through `alloc`, `free`, `load` and
`store`, and treats them opaquely: no step compares two locations or computes one.  The host
step's arguments and results are integer literals and booleans, and renaming fixes them
(`host_call_rename`).  The array steps compute locations: `tab` places a run of consecutive
cells, and `idx` and `drop` add an index to a base.  A permutation of `Loc` does not preserve
`ℓ + i`, so the results here are stated for steps whose redex is not an array step
(`FrameTheorems.ArrRedex`), and runs of such steps (`StepsR`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa

/-! ### Renaming a term -/

/-- `e` with every location `ℓ` replaced by `σ ℓ`. -/
def Expr.rename (σ : Loc → Loc) : Expr → Expr
  | .var i         => .var i
  | .unit          => .unit
  | .pair e₁ e₂    => .pair (e₁.rename σ) (e₂.rename σ)
  | .inj₁ e        => .inj₁ (e.rename σ)
  | .inj₂ e        => .inj₂ (e.rename σ)
  | .lam b         => .lam (b.rename σ)
  | .loc ℓ         => .loc (σ ℓ)
  | .prim p        => .prim p
  | .seq e₁ e₂     => .seq (e₁.rename σ) (e₂.rename σ)
  | .letpair e₁ e₂ => .letpair (e₁.rename σ) (e₂.rename σ)
  | .case e e₁ e₂  => .case (e.rename σ) (e₁.rename σ) (e₂.rename σ)
  | .app f a       => .app (f.rename σ) (a.rename σ)

theorem IsVal.rename {e : Expr} (h : IsVal e) (σ : Loc → Loc) : IsVal (e.rename σ) := by
  induction h with
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | inj₁ _ ih => exact .inj₁ ih
  | inj₂ _ ih => exact .inj₂ ih
  | lam => exact .lam
  | loc => exact .loc
  | prim => exact .prim
  | storeV _ ih => exact .storeV ih

/-- Renaming changes no term into a value. -/
theorem isVal_of_rename (σ : Loc → Loc) : ∀ {e : Expr}, IsVal (e.rename σ) → IsVal e
  | .unit, _ => .unit
  | .pair _ _, h => .pair (isVal_of_rename σ h.pair_left) (isVal_of_rename σ h.pair_right)
  | .inj₁ _, h => .inj₁ (isVal_of_rename σ h.inj₁_inv)
  | .inj₂ _, h => .inj₂ (isVal_of_rename σ h.inj₂_inv)
  | .lam _, _ => .lam
  | .loc _, _ => .loc
  | .prim _, _ => .prim
  | .app f _, h => by
      have hf := h.app_fun
      cases f with
      | prim p =>
          simp only [Expr.rename, Expr.prim.injEq] at hf
          subst hf
          exact .storeV (isVal_of_rename σ h.app_arg)
      | _ => simp [Expr.rename] at hf
  | .var _, h | .seq _ _, h | .letpair _ _, h | .case _ _ _, h => by
      simp [Expr.rename] at h

/-- `v` with every location `ℓ` replaced by `σ ℓ`. -/
def Val.rename (σ : Loc → Loc) (v : Val) : Val := ⟨v.1.rename σ, v.2.rename σ⟩

@[simp] theorem Val.rename_val (σ : Loc → Loc) (v : Val) : (v.rename σ).1 = v.1.rename σ := rfl

theorem Expr.rename_comp (σ τ : Loc → Loc) :
    ∀ e : Expr, (e.rename σ).rename τ = e.rename (τ ∘ σ)
  | .var _ | .unit | .prim _ | .loc _ => rfl
  | .pair a b | .seq a b | .letpair a b | .app a b => by
      simp only [Expr.rename, Expr.rename_comp σ τ a, Expr.rename_comp σ τ b]
  | .inj₁ a | .inj₂ a | .lam a => by simp only [Expr.rename, Expr.rename_comp σ τ a]
  | .case a b c => by
      simp only [Expr.rename, Expr.rename_comp σ τ a, Expr.rename_comp σ τ b,
        Expr.rename_comp σ τ c]

theorem Expr.rename_id : ∀ e : Expr, e.rename id = e
  | .var _ | .unit | .prim _ | .loc _ => rfl
  | .pair a b | .seq a b | .letpair a b | .app a b => by
      simp only [Expr.rename, Expr.rename_id a, Expr.rename_id b]
  | .inj₁ a | .inj₂ a | .lam a => by simp only [Expr.rename, Expr.rename_id a]
  | .case a b c => by simp only [Expr.rename, Expr.rename_id a, Expr.rename_id b, Expr.rename_id c]

theorem Val.rename_comp (σ τ : Loc → Loc) (v : Val) :
    (v.rename σ).rename τ = v.rename (τ ∘ σ) := Subtype.ext (Expr.rename_comp σ τ v.1)

theorem Val.rename_id (v : Val) : v.rename id = v := Subtype.ext (Expr.rename_id v.1)

/-- `ℓ` occurs in `e`. -/
def Expr.Occ (ℓ : Loc) : Expr → Prop
  | .var _ | .unit | .prim _ => False
  | .loc k         => k = ℓ
  | .pair a b | .seq a b | .letpair a b | .app a b => a.Occ ℓ ∨ b.Occ ℓ
  | .inj₁ a | .inj₂ a | .lam a => a.Occ ℓ
  | .case a b c    => a.Occ ℓ ∨ b.Occ ℓ ∨ c.Occ ℓ

/-- Renamings that agree on the locations of `e` rename it alike. -/
theorem Expr.rename_congr {σ τ : Loc → Loc} :
    ∀ e : Expr, (∀ ℓ, e.Occ ℓ → σ ℓ = τ ℓ) → e.rename σ = e.rename τ
  | .var _, _ | .unit, _ | .prim _, _ => rfl
  | .loc k, h => by simp only [Expr.rename, h k rfl]
  | .pair a b, h | .seq a b, h | .letpair a b, h | .app a b, h => by
      simp only [Expr.rename, Expr.rename_congr a (fun ℓ o => h ℓ (Or.inl o)),
        Expr.rename_congr b (fun ℓ o => h ℓ (Or.inr o))]
  | .inj₁ a, h | .inj₂ a, h | .lam a, h => by
      simp only [Expr.rename, Expr.rename_congr a h]
  | .case a b c, h => by
      simp only [Expr.rename, Expr.rename_congr a (fun ℓ o => h ℓ (Or.inl o)),
        Expr.rename_congr b (fun ℓ o => h ℓ (Or.inr (Or.inl o))),
        Expr.rename_congr c (fun ℓ o => h ℓ (Or.inr (Or.inr o)))]

theorem Expr.rename_eq_self {σ : Loc → Loc} (e : Expr) (h : ∀ ℓ, e.Occ ℓ → σ ℓ = ℓ) :
    e.rename σ = e :=
  (Expr.rename_congr (τ := id) e h).trans (Expr.rename_id e)

theorem Expr.occ_rename {σ : Loc → Loc} {ℓ : Loc} :
    ∀ e : Expr, (e.rename σ).Occ ℓ ↔ ∃ k, e.Occ k ∧ σ k = ℓ
  | .var _ | .unit | .prim _ => by simp [Expr.rename, Expr.Occ]
  | .loc k => by simp [Expr.rename, Expr.Occ]
  | .pair a b | .seq a b | .letpair a b | .app a b => by
      simp only [Expr.rename, Expr.Occ, Expr.occ_rename a, Expr.occ_rename b]
      constructor
      · rintro (⟨k, h, rfl⟩ | ⟨k, h, rfl⟩)
        · exact ⟨k, .inl h, rfl⟩
        · exact ⟨k, .inr h, rfl⟩
      · rintro ⟨k, h | h, rfl⟩
        · exact .inl ⟨k, h, rfl⟩
        · exact .inr ⟨k, h, rfl⟩
  | .inj₁ a | .inj₂ a | .lam a => by simp only [Expr.rename, Expr.Occ, Expr.occ_rename a]
  | .case a b c => by
      simp only [Expr.rename, Expr.Occ, Expr.occ_rename a, Expr.occ_rename b, Expr.occ_rename c]
      constructor
      · rintro (⟨k, h, rfl⟩ | ⟨k, h, rfl⟩ | ⟨k, h, rfl⟩)
        · exact ⟨k, .inl h, rfl⟩
        · exact ⟨k, .inr (.inl h), rfl⟩
        · exact ⟨k, .inr (.inr h), rfl⟩
      · rintro ⟨k, h | h | h, rfl⟩
        · exact .inl ⟨k, h, rfl⟩
        · exact .inr (.inl ⟨k, h, rfl⟩)
        · exact .inr (.inr ⟨k, h, rfl⟩)

/-! ### Renaming commutes with shifting and substitution -/

theorem Expr.rename_shift (σ : Loc → Loc) :
    ∀ (d c : Nat) (e : Expr), (e.shift d c).rename σ = (e.rename σ).shift d c
  | d, c, .var i => by
      by_cases h : i < c <;> simp [Expr.shift, Expr.rename, h]
  | _, _, .unit | _, _, .prim _ | _, _, .loc _ => rfl
  | d, c, .pair a b | d, c, .seq a b | d, c, .app a b => by
      simp only [Expr.shift, Expr.rename, Expr.rename_shift σ d c a, Expr.rename_shift σ d c b]
  | d, c, .letpair a b => by
      simp only [Expr.shift, Expr.rename, Expr.rename_shift σ d c a,
        Expr.rename_shift σ d (c + 2) b]
  | d, c, .inj₁ a | d, c, .inj₂ a => by
      simp only [Expr.shift, Expr.rename, Expr.rename_shift σ d c a]
  | d, c, .lam a => by simp only [Expr.shift, Expr.rename, Expr.rename_shift σ d (c + 1) a]
  | d, c, .case a b e => by
      simp only [Expr.shift, Expr.rename, Expr.rename_shift σ d c a,
        Expr.rename_shift σ d (c + 1) b, Expr.rename_shift σ d (c + 1) e]

theorem Val.rename_shift (σ : Loc → Loc) (d c : Nat) (v : Val) :
    (v.shift d c).rename σ = (v.rename σ).shift d c :=
  Subtype.ext (Expr.rename_shift σ d c v.1)

theorem Expr.rename_subst (σ : Loc → Loc) :
    ∀ (j : Nat) (s : Val) (e : Expr), (e.subst j s).rename σ = (e.rename σ).subst j (s.rename σ)
  | j, s, .var i => by
      simp only [Expr.subst, Expr.rename]
      split
      · rfl
      · split <;> rfl
  | _, _, .unit | _, _, .prim _ | _, _, .loc _ => rfl
  | j, s, .pair a b | j, s, .seq a b | j, s, .app a b => by
      simp only [Expr.subst, Expr.rename, Expr.rename_subst σ j s a, Expr.rename_subst σ j s b]
  | j, s, .letpair a b => by
      simp only [Expr.subst, Expr.rename, Expr.rename_subst σ j s a,
        Expr.rename_subst σ (j + 2) (s.shift 2 0) b, Val.rename_shift]
  | j, s, .inj₁ a | j, s, .inj₂ a => by
      simp only [Expr.subst, Expr.rename, Expr.rename_subst σ j s a]
  | j, s, .lam a => by
      simp only [Expr.subst, Expr.rename, Expr.rename_subst σ (j + 1) (s.shift 1 0) a,
        Val.rename_shift]
  | j, s, .case a b e => by
      simp only [Expr.subst, Expr.rename, Expr.rename_subst σ j s a,
        Expr.rename_subst σ (j + 1) (s.shift 1 0) b, Expr.rename_subst σ (j + 1) (s.shift 1 0) e,
        Val.rename_shift]

/-! ### The host step is location-free -/

theorem Expr.lit?_rename (σ : Loc → Loc) (e : Expr) : (e.rename σ).lit? = e.lit? := by
  cases e with
  | prim p => cases p <;> rfl
  | _ => rfl

theorem Expr.arg32?_rename (σ : Loc → Loc) (e : Expr) : (e.rename σ).arg32? = e.arg32? := by
  simp only [Expr.arg32?, Expr.lit?_rename]

theorem Expr.arg64?_rename (σ : Loc → Loc) (e : Expr) : (e.rename σ).arg64? = e.arg64? := by
  simp only [Expr.arg64?, Expr.lit?_rename]

theorem Expr.args32?_rename (σ : Loc → Loc) (e : Expr) : (e.rename σ).args32? = e.args32? := by
  cases e with
  | pair a b => simp only [Expr.rename, Expr.args32?, Expr.arg32?_rename]
  | _ => rfl

theorem Expr.args64?_rename (σ : Loc → Loc) (e : Expr) : (e.rename σ).args64? = e.args64? := by
  cases e with
  | pair a b => simp only [Expr.rename, Expr.args64?, Expr.arg64?_rename]
  | _ => rfl

theorem Val.rename_i32 (σ : Loc → Loc) (n : UInt32) : (Val.i32 n).rename σ = .i32 n := rfl
theorem Val.rename_i64 (σ : Loc → Loc) (n : UInt64) : (Val.i64 n).rename σ = .i64 n := rfl
theorem Val.rename_bool (σ : Loc → Loc) (b : Bool) : (Val.bool b).rename σ = .bool b := by
  cases b <;> rfl
theorem Val.rename_opt (σ : Loc → Loc) (o : Option Val)
    (h : ∀ v, o = some v → v.rename σ = v) : (Val.opt o).rename σ = .opt o := by
  cases o with
  | none => rfl
  | some v => exact Subtype.ext (by
      show Expr.inj₁ (v.1.rename σ) = .inj₁ v.1
      rw [← Val.rename_val, h v rfl])

set_option linter.unnecessarySeqFocus false in
/-- **The host step is location-free.**  Renaming an argument does not change the result, and
renaming fixes every result. -/
theorem host_call_rename (H : Host) (op : HostOp) (σ : Loc → Loc) (v : Val) :
    H.call op (v.rename σ) = H.call op v ∧ ∀ r, H.call op v = some r → r.rename σ = r := by
  cases op with
  | bin w o => cases w <;> refine ⟨by simp only [Host.call, Val.rename_val, Expr.args32?_rename,
      Expr.args64?_rename], ?_⟩ <;> intro r h <;> simp only [Host.call, Option.map_eq_some_iff] at h <;>
      obtain ⟨_, _, rfl⟩ := h <;> rfl
  | div w o => cases w <;> refine ⟨by simp only [Host.call, Val.rename_val, Expr.args32?_rename,
      Expr.args64?_rename], ?_⟩ <;> intro r h <;> simp only [Host.call, Option.map_eq_some_iff] at h <;>
      obtain ⟨_, _, rfl⟩ := h <;>
      exact Val.rename_opt σ _ (fun v hv => by
        simp only [Option.map_eq_some_iff] at hv; obtain ⟨_, _, rfl⟩ := hv; rfl)
  | un w o => cases w <;> refine ⟨by simp only [Host.call, Val.rename_val, Expr.arg32?_rename,
      Expr.arg64?_rename], ?_⟩ <;> intro r h <;> simp only [Host.call, Option.map_eq_some_iff] at h <;>
      obtain ⟨_, _, rfl⟩ := h <;> rfl
  | eqz w => cases w <;> refine ⟨by simp only [Host.call, Val.rename_val, Expr.arg32?_rename,
      Expr.arg64?_rename], ?_⟩ <;> intro r h <;> simp only [Host.call, Option.map_eq_some_iff] at h <;>
      obtain ⟨_, _, rfl⟩ := h <;> exact Val.rename_bool σ _
  | rel w o => cases w <;> refine ⟨by simp only [Host.call, Val.rename_val, Expr.args32?_rename,
      Expr.args64?_rename], ?_⟩ <;> intro r h <;> simp only [Host.call, Option.map_eq_some_iff] at h <;>
      obtain ⟨_, _, rfl⟩ := h <;> exact Val.rename_bool σ _
  | _ => refine ⟨by simp only [Host.call, Val.rename_val, Expr.arg32?_rename,
      Expr.arg64?_rename], ?_⟩ <;> intro r h <;> simp only [Host.call, Option.map_eq_some_iff] at h <;>
      obtain ⟨_, _, rfl⟩ := h <;> rfl

end BoCa

namespace BoCa.BoLo

/-! ### Renaming a context and a heap -/

/-- `K` with every location `ℓ` replaced by `σ ℓ`. -/
def Kont.rename (σ : Loc → Loc) : Kont → Kont
  | .hole          => .hole
  | .pairL K e     => .pairL (K.rename σ) (e.rename σ)
  | .pairR v K     => .pairR (v.rename σ) (K.rename σ)
  | .letpair K e   => .letpair (K.rename σ) (e.rename σ)
  | .case K e₁ e₂  => .case (K.rename σ) (e₁.rename σ) (e₂.rename σ)
  | .appR f K      => .appR (f.rename σ) (K.rename σ)
  | .appL K v      => .appL (K.rename σ) (v.rename σ)
  | .seq K e       => .seq (K.rename σ) (e.rename σ)
  | .inj₁ K        => .inj₁ (K.rename σ)
  | .inj₂ K        => .inj₂ (K.rename σ)

theorem Kont.rename_plug (σ : Loc → Loc) (K : Kont) (e : Expr) :
    (K.plug e).rename σ = (K.rename σ).plug (e.rename σ) := by
  induction K with
  | hole => rfl
  | _ => simp_all [Kont.plug, Kont.rename, Expr.rename]

/-- The cell at `ℓ` moved to `σ ℓ`, its value renamed. -/
def Heap.rename (σ : Equiv.Perm Loc) (μ : Heap) : Heap := fun ℓ => (μ (σ.symm ℓ)).map (Val.rename σ)

@[simp] theorem Heap.rename_apply (σ : Equiv.Perm Loc) (μ : Heap) (ℓ : Loc) :
    μ.rename σ (σ ℓ) = (μ ℓ).map (Val.rename σ) := by
  simp [Heap.rename]

theorem Heap.rename_upd (σ : Equiv.Perm Loc) (μ : Heap) (ℓ : Loc) (v : Val) :
    (μ.upd ℓ v).rename σ = (μ.rename σ).upd (σ ℓ) (v.rename σ) := by
  funext k
  simp only [Heap.rename, Heap.upd]
  by_cases h : k = σ ℓ
  · subst h; simp
  · have : σ.symm k ≠ ℓ := fun e => h (by rw [← e]; simp)
    simp [h, this]

theorem Heap.rename_del (σ : Equiv.Perm Loc) (μ : Heap) (ℓ : Loc) :
    (μ.del ℓ).rename σ = (μ.rename σ).del (σ ℓ) := by
  funext k
  simp only [Heap.rename, Heap.del]
  by_cases h : k = σ ℓ
  · subst h; simp
  · have : σ.symm k ≠ ℓ := fun e => h (by rw [← e]; simp)
    simp [h, this]

theorem Heap.rename_mul (σ τ : Equiv.Perm Loc) (μ : Heap) :
    (μ.rename σ).rename τ = μ.rename (τ * σ) := by
  funext k
  simp only [Heap.rename, Option.map_map, Equiv.Perm.mul_def, Equiv.symm_trans_apply]
  congr 1
  funext v
  simp only [Function.comp, Val.rename_comp]
  rfl

theorem Heap.rename_one (μ : Heap) : μ.rename 1 = μ := by
  funext k
  show (μ k).map (Val.rename id) = μ k
  cases μ k with
  | none => rfl
  | some v => exact congrArg some (Val.rename_id v)

/-! ### Runs are invariant under renaming -/

open BoCa.Fig16.LogRel.Core.FrameTheorems (ArrRedex arrRedex_tab arrRedex_idx arrRedex_drop)

/-- A redex `p v` at a primitive that is not an array step is not an array redex. -/
theorem not_arrRedex_prim {p : Prim} (hp : p ≠ .tab ∧ p ≠ .idx ∧ p ≠ .drop) (v : Val) :
    ¬ ArrRedex (.app (.val (.prim p)) (.val v)) := by
  rintro ⟨q, w, hq, h⟩
  simp only [Expr.val, Val.prim, Expr.app.injEq, Expr.prim.injEq] at h
  rcases hq with rfl | rfl | rfl
  · exact hp.1 h.1
  · exact hp.2.1 h.1
  · exact hp.2.2 h.1

/-- Renaming makes no term an array redex. -/
theorem not_arrRedex_rename (σ : Loc → Loc) {a : Expr} (hnr : ¬ ArrRedex a) :
    ¬ ArrRedex (a.rename σ) := by
  rintro ⟨p, v, hp, h⟩
  cases a with
  | app f x =>
      simp only [Expr.rename, Expr.app.injEq] at h
      obtain ⟨h₁, h₂⟩ := h
      cases f with
      | prim q =>
          simp only [Expr.rename, Expr.val, Val.prim, Expr.prim.injEq] at h₁
          have hx : IsVal x := isVal_of_rename σ (h₂ ▸ v.2)
          exact hnr ⟨p, ⟨x, hx⟩, hp, by rw [h₁]; rfl⟩
      | _ => simp [Expr.rename, Expr.val, Val.prim] at h₁
  | _ => simp [Expr.rename] at h

/-- **A head step, renamed, is a head step**, when its redex is not an array step. -/
theorem head_rename (σ : Equiv.Perm Loc) {μ μ' : Heap} {a a' : Expr} (h : Head μ a μ' a')
    (hnr : ¬ ArrRedex a) :
    Head (μ.rename σ) (a.rename σ) (μ'.rename σ) (a'.rename σ) := by
  cases h with
  | tab => exact absurd (arrRedex_tab _) hnr
  | idx => exact absurd (arrRedex_idx _) hnr
  | drop => exact absurd (arrRedex_drop _) hnr
  | beta b v =>
      rw [Expr.rename_subst]
      exact .beta _ (b.rename σ) (v.rename σ)
  | alloc v ℓ h =>
      rw [Heap.rename_upd]
      exact .alloc _ (v.rename σ) (σ ℓ) (by simp [h])
  | free ℓ v h =>
      rw [Heap.rename_del]
      exact .free _ (σ ℓ) (v.rename σ) (by simp [h])
  | load ℓ v h => exact .load _ (σ ℓ) (v.rename σ) (by simp [h])
  | store ℓ v w h =>
      rw [Heap.rename_upd]
      exact .store _ (σ ℓ) (v.rename σ) (w.rename σ) (by simp [h])
  | seq => exact .seq _ _
  | letpair v₁ v₂ e =>
      rw [Expr.rename_subst, Expr.rename_subst, Val.rename_shift]
      exact .letpair _ (v₁.rename σ) (v₂.rename σ) (e.rename σ)
  | case₁ v e₁ e₂ =>
      rw [Expr.rename_subst]
      exact .case₁ _ (v.rename σ) (e₁.rename σ) (e₂.rename σ)
  | case₂ v e₁ e₂ =>
      rw [Expr.rename_subst]
      exact .case₂ _ (v.rename σ) (e₁.rename σ) (e₂.rename σ)
  | host op v r h =>
      obtain ⟨h₁, h₂⟩ := host_call_rename ℍ op σ v
      have hr : (Expr.val r).rename σ = Expr.val r := by
        rw [← Val.rename_val, h₂ r h]
      rw [hr]
      exact .host _ op (v.rename σ) r (h₁.trans h)

/-- A step whose redex is not an array step. -/
def Step1R (μ : Heap) (e : Expr) (μ' : Heap) (e' : Expr) : Prop :=
  ∃ (K : Kont) (a a' : Expr), e = K.plug a ∧ e' = K.plug a' ∧ Head μ a μ' a' ∧ ¬ ArrRedex a

theorem Step1R.toStep1 {μ μ' : Heap} {e e' : Expr} (h : Step1R μ e μ' e') : Step1 μ e μ' e' := by
  obtain ⟨K, a, a', h₁, h₂, h₃, -⟩ := h
  exact ⟨K, a, a', h₁, h₂, h₃⟩

/-- A run that takes no array step. -/
inductive StepsR : Heap → Expr → Heap → Expr → Prop where
  | refl (μ : Heap) (e : Expr) : StepsR μ e μ e
  | more {μ μ₁ μ' : Heap} {e e₁ e' : Expr}
      (h : Step1R μ e μ₁ e₁) (t : StepsR μ₁ e₁ μ' e') : StepsR μ e μ' e'

theorem step1_rename (σ : Equiv.Perm Loc) {μ μ' : Heap} {e e' : Expr} (h : Step1R μ e μ' e') :
    Step1R (μ.rename σ) (e.rename σ) (μ'.rename σ) (e'.rename σ) := by
  obtain ⟨K, a, a', rfl, rfl, hh, hnr⟩ := h
  exact ⟨K.rename σ, a.rename σ, a'.rename σ, Kont.rename_plug σ K a, Kont.rename_plug σ K a',
    head_rename σ hh hnr, not_arrRedex_rename σ hnr⟩

/-- **Runs with no array step are invariant under renaming.**  For a permutation `σ` of the
locations, such a run from `(μ, e)` to `(μ', e')` renames to one from `(σ μ, σ e)` to
`(σ μ', σ e')`. -/
theorem steps_rename (σ : Equiv.Perm Loc) {μ μ' : Heap} {e e' : Expr} (h : StepsR μ e μ' e') :
    StepsR (μ.rename σ) (e.rename σ) (μ'.rename σ) (e'.rename σ) := by
  induction h with
  | refl => exact .refl _ _
  | more h _ ih => exact .more (step1_rename σ h) ih

end BoCa.BoLo

end
