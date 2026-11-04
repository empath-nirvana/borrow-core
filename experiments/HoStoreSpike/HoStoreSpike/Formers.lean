import HoStoreSpike.Reread

/-!
# Formers of the higher-order store, and guarded recursion (spike, #790)

* `HTy.unit`, `HTy.imm a τ` (a view), `HTy.mut a τ` at **any** `HTy` `τ`, and `HTy.thunk Φ`, the
  guarded Kripke closure of **any** predicate family `Φ`: at index `n`, `Φ` at every `k < n`, every
  later tree, every store typing keeping the held cells' types to `k`, and every re-reading. A
  thunk, task or stored continuation is `thunk Φ` with `Φ` its run (the relation at index `k`);
  `Φ` needs no law (`HTy.thunk_lawful`).
* `Mut`'s laws need nothing of its payload (`HTy.mut_lawful`): its payload's laws are spent where
  the cell is re-read (`cellInv_extend`), at the store typing's lawfulness.
* **Guarded recursion** (`HTy.gfix`): every contractive `F` (`(F τ).ap (n+1)` read off `τ.ap n`)
  has a fixed point, `(gfix F).Q = (F (gfix F)).Q`. `mut` and `thunk` are contractive
  (`HTy.mut_contr`, `HTy.thunk_contr`), so `μX. Mut a (thunk X)`, a cell holding a task that
  returns such a cell, at every depth, is a lawful type (`cellTask_lawful`).
-/

noncomputable section

namespace BoCa.Fig16.Tree.HoStore
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp

/-! ### Options of approximations -/

theorem map_ap_le {o o' : Option HTy} {n k : Nat}
    (h : o.map (fun τ => τ.ap n) = o'.map (fun τ => τ.ap n)) (hk : k ≤ n) :
    o.map (fun τ => τ.ap k) = o'.map (fun τ => τ.ap k) := by
  cases o <;> cases o' <;> simp only [Option.map_none, Option.map_some, reduceCtorEq,
    Option.some.injEq] at h ⊢
  exact HTy.ap_le h hk

/-- The approximations agreeing at every `k < n` are one at `n`. -/
theorem HTy.ap_eq_of_Q {τ σ : HTy} : ∀ {n : Nat}, (∀ k < n, τ.Q k = σ.Q k) → τ.ap n = σ.ap n
  | 0, _ => rfl
  | n + 1, h => by
      show (τ.ap n, τ.Q n) = (σ.ap n, σ.Q n)
      rw [HTy.ap_eq_of_Q (fun k hk => h k (by omega)), h n (by omega)]

/-! ### `1` and `Imm` -/

/-- `𝒱⟦1⟧`. -/
def HTy.unit : HTy := ⟨fun _ _ _ v ρ => v = BoCa.Val.unit ∧ ρ = PMap.empty⟩

theorem HTy.unit_lawful : HTy.unit.Lawful where
  down _ _ _ _ _ h := h
  mono := by
    rintro n K K' Ψ Ψ' j v ρ ρ' - - hr ⟨hv, rfl⟩
    exact ⟨hv, RR.of_empty hr⟩

/-- `𝒱⟦Imm @a τ⟧`: a view `ℓ ↦ imm(β̄, w, χ)` with `a ⊑ β̄` and the payload in `τ` at the same index. -/
def HTy.imm (a : Life) (τ : HTy) : HTy :=
  ⟨fun n K Ψa v ρ => ∃ (l : BoCa.Loc) (i : TImm K), v = BoCa.Val.loc l ∧
    ρ = PMap.sng l (.imm i) ∧ (∀ x ∈ i.ls.set, K.le a x) ∧ τ.Q n K Ψa i.v i.res⟩

theorem HTy.imm_lawful (a : Life) {τ : HTy} (hτ : τ.Lawful) : (HTy.imm a τ).Lawful where
  down := by
    rintro n K Ψ v ρ ⟨l, i, rfl, rfl, hle, hP⟩
    exact ⟨l, i, rfl, rfl, hle, hτ.down n K Ψ i.v i.res hP⟩
  mono := by
    rintro n K K' Ψ Ψ' j v ρ ρ' hE hag hr ⟨l, i, rfl, rfl, hle, hP⟩
    obtain ⟨ψ', rfl, hrc⟩ := RR.of_sng hr
    have e : (PMap.sng l (CellUT.imm i) : TRes K).get l = some (.imm i) := by
      simp [PMap.sng_get]
    cases hrc with
    | imm _ _ i' hs hv hdom hw =>
        refine ⟨l, i', rfl, rfl, fun x hx => hE.le (hle x (hs ▸ hx)), ?_⟩
        rw [hv]
        exact hτ.mono n K K' Ψ Ψ' j _ _ _ hE (hag.wit e) ⟨hdom, hw⟩ hP

/-! ### `Mut` at any semantic type -/

/-- **`𝒱⟦Mut @a τ⟧` at any `τ`**: a cell `ℓ ↦ mut(β̄, …)` with `a ⊑ β̄`, whose location the store
typing gives `τ` to index `n`. The cell's invariant is the world's (`Cov` at `semH Ψ n`): `τ` one
step later. -/
def HTy.mut (a : Life) (τ : HTy) : HTy :=
  ⟨fun n K Ψa v ρ => ∃ (l : BoCa.Loc) (c : TMut K), v = BoCa.Val.loc l ∧
    ρ = PMap.sng l (.mut c) ∧ Ψa l = some (τ.ap n) ∧ ∀ x ∈ c.ls.set, K.le a x⟩

/-- **`Mut @a τ` is lawful at every `τ`.** -/
theorem HTy.mut_lawful (a : Life) (τ : HTy) : (HTy.mut a τ).Lawful where
  down := by
    rintro n K Ψ v ρ ⟨l, c, rfl, rfl, hl, hle⟩
    refine ⟨l, c, rfl, rfl, ?_, hle⟩
    have h : (Ψ l).map (fun σ => σ.ap (n + 1)) = (some τ).map (fun σ => σ.ap (n + 1)) := hl
    exact map_ap_le h (Nat.le_succ n)
  mono := by
    rintro n K K' Ψ Ψ' j v ρ ρ' hE hag hr ⟨l, c, rfl, rfl, hl, hle⟩
    obtain ⟨ψ', rfl, hrc⟩ := RR.of_sng hr
    have hl' : Ψ' l = Ψ l := hag l (.top (m := c) (by simp [PMap.sng_get]))
    cases hrc with
    | «mut» _ _ c' _ _ hs =>
        refine ⟨l, c', rfl, rfl, ?_, fun x hx => ?_⟩
        · show (Ψ' l).map _ = _; rw [hl']; exact hl
        · rw [hs] at hx; exact hE.le (hle x (K'.minS_sub hx))

/-! ### Thunks: the guarded Kripke closure of any predicate family -/

/-- `o` (an approximation at `n`) and `o′` agree to index `k`. -/
def OAg {n : Nat} (o : Option (ATy n)) (k : Nat) (o' : Option HTy) : Prop :=
  ∃ σ : Option HTy, o = σ.map (fun τ => τ.ap n) ∧
    σ.map (fun τ => τ.ap k) = o'.map (fun τ => τ.ap k)

/-- **A thunk of `Φ`**: at index `n`, `Φ` at every `k < n` (one step later at least), at every
later tree, every store typing keeping the types of the held cells to `k`, and every re-reading. -/
def HTy.thunk (Φ : HTy) : HTy :=
  ⟨fun n K Ψa v ρ => ∀ k < n, ∀ (K' : WCactus) (Ψ' : HStore) (j : Nat) (ρ' : TRes K'),
    K.Ext K' → (∀ l, HoldsMut ρ l → OAg (Ψa l) k (Ψ' l)) → RR (semH Ψ' j) ρ ρ' →
      Φ.P k K' Ψ' v ρ'⟩

/-- **A thunk type is lawful at every `Φ`.** -/
theorem HTy.thunk_lawful (Φ : HTy) : (HTy.thunk Φ).Lawful where
  down := by
    intro n K Ψ v ρ h k hk K' Ψ' j ρ' hE hag hr
    refine h k (by omega) K' Ψ' j ρ' hE (fun l hl => ?_) hr
    obtain ⟨σ, e₁, e₂⟩ := hag l hl
    refine ⟨Ψ l, rfl, ?_⟩
    have : (Ψ l).map (fun τ => τ.ap n) = σ.map (fun τ => τ.ap n) := e₁
    exact (map_ap_le this (by omega)).trans e₂
  mono := by
    intro n K₁ K₂ Ψ₁ Ψ₂ j₂ v ρ₁ ρ₂ hE₁₂ hag₁₂ hr₁₂ h k hk K₃ Ψ₃ j₃ ρ₃ hE₂₃ hag₂₃ hr₂₃
    refine h k hk K₃ Ψ₃ j₃ ρ₃ (WCactus.Ext.trans hE₁₂ hE₂₃) (fun l hl => ?_)
      (RR.trans_retype hE₂₃ hr₁₂ hr₂₃)
    obtain ⟨σ, e₁, e₂⟩ := hag₂₃ l (hl.rr hr₁₂)
    refine ⟨σ, ?_, e₂⟩
    have : Ψ₂.ap n l = Ψ₁.ap n l := by
      show (Ψ₂ l).map _ = (Ψ₁ l).map _; rw [hag₁₂ l hl]
    rw [← this]; exact e₁

/-! ### The relation's runs read the store typing only to the index -/

/-- **The location typing at index `n`, from the store typing's approximation at `n`.** -/
def semA : (n : Nat) → (BoCa.Loc → Option (ATy n)) → LocTy
  | 0, Ψa => fun l => (Ψa l).map (fun _ => ⟨fun _ _ _ => True⟩)
  | _k + 1, Ψa => fun l => (Ψa l).map (fun a =>
      ⟨fun K v ρ => a.2 K (fun l' => (Ψa l').map Prod.fst) v ρ⟩)

/-- **The world a run at index `n` reads is read off the approximation at `n`**: `semH Ψ n` is
`semA n (Ψ.ap n)`. So `Cov`, `RC`, `RR` at `semH Ψ n` see the store typing only to `n`. -/
theorem semH_eq_semA (Ψ : HStore) : ∀ n, semH Ψ n = semA n (Ψ.ap n)
  | 0 => by
      funext l
      cases e : Ψ l <;> simp [semH, semA, HStore.ap, e, cellInv]
  | k + 1 => by
      funext l
      have hres : (fun l' => (Ψ.ap (k + 1) l').map Prod.fst) = Ψ.ap k := by
        funext l'; simp only [HStore.ap]; cases Ψ l' <;> rfl
      show semH Ψ (k + 1) l = (Ψ.ap (k + 1) l).map _
      cases e : Ψ l with
      | none => simp [semH, HStore.ap, e]
      | some τ =>
          have hl : Ψ.ap (k + 1) l = some (τ.ap (k + 1)) := by simp [HStore.ap, e]
          rw [semH_of e, hl, Option.map_some, hres]
          rfl

/-- **A predicate of the world's location typing is a semantic type**: a run of the relation at
index `n` that reads the world at `semH Ψ n` (its cells at their invariants) is `HTy.ofLocTy`. -/
def HTy.ofLocTy (R : (n : Nat) → (K : WCactus) → LocTy → BoCa.Val → TRes K → Prop) : HTy :=
  ⟨fun n K Ψa v ρ => R n K (semA n Ψa) v ρ⟩

theorem HTy.ofLocTy_P (R : (n : Nat) → (K : WCactus) → LocTy → BoCa.Val → TRes K → Prop)
    (n : Nat) (K : WCactus) (Ψ : HStore) (v : BoCa.Val) (ρ : TRes K) :
    (HTy.ofLocTy R).P n K Ψ v ρ ↔ R n K (semH Ψ n) v ρ := by
  rw [semH_eq_semA]; rfl

/-- **A thunk whose run reads the world is lawful, at every run.** -/
theorem HTy.thunk_run_lawful (R : (n : Nat) → (K : WCactus) → LocTy → BoCa.Val → TRes K → Prop) :
    (HTy.thunk (HTy.ofLocTy R)).Lawful :=
  HTy.thunk_lawful _

/-! ### Contractive formers -/

/-- `F` reads `τ` one step later. -/
def Contractive (F : HTy → HTy) : Prop :=
  ∀ τ σ n, τ.ap n = σ.ap n → (F τ).ap (n + 1) = (F σ).ap (n + 1)

theorem HTy.mut_contr (a : Life) : Contractive (HTy.mut a) := by
  intro τ σ n h
  refine HTy.ap_eq_of_Q fun k hk => ?_
  have hk' : τ.ap k = σ.ap k := HTy.ap_le h (by omega)
  unfold HTy.mut
  dsimp only
  rw [hk']

theorem HTy.thunk_contr : Contractive HTy.thunk := by
  intro τ σ n h
  refine HTy.ap_eq_of_Q fun k hk => ?_
  have hQ : ∀ k' < k, τ.Q k' = σ.Q k' := fun k' hk' => HTy.Q_eq_of_ap h (by omega)
  funext K Ψa v ρ
  apply propext
  unfold HTy.thunk HTy.P
  constructor
  · intro H k' hk' K' Ψ' j ρ' a b c; rw [← hQ k' hk']; exact H k' hk' K' Ψ' j ρ' a b c
  · intro H k' hk' K' Ψ' j ρ' a b c; rw [hQ k' hk']; exact H k' hk' K' Ψ' j ρ' a b c

theorem Contractive.comp_left {F G : HTy → HTy} (hF : Contractive F)
    (hG : ∀ τ σ n, τ.ap n = σ.ap n → (G τ).ap n = (G σ).ap n) : Contractive (F ∘ G) :=
  fun τ σ n h => hF _ _ n (hG τ σ n h)

/-- A contractive former is non-expansive. -/
theorem Contractive.nonexp {F : HTy → HTy} (hF : Contractive F) :
    ∀ τ σ n, τ.ap n = σ.ap n → (F τ).ap n = (F σ).ap n := by
  intro τ σ n h
  cases n with
  | zero => rfl
  | succ n => exact hF τ σ n (HTy.ap_le h (Nat.le_succ n))

/-! ### Guarded recursion -/

/-- The iterates of `F` from the empty type. -/
def HTy.iter (F : HTy → HTy) : Nat → HTy
  | 0 => ⟨fun _ _ _ _ _ => False⟩
  | i + 1 => F (HTy.iter F i)

theorem HTy.iter_stable {F : HTy → HTy} (hF : Contractive F) :
    ∀ i, (HTy.iter F i).ap i = (HTy.iter F (i + 1)).ap i
  | 0 => rfl
  | i + 1 => hF _ _ i (HTy.iter_stable hF i)

/-- **The guarded fixed point**: at index `n`, the `n+1`-st iterate. -/
def HTy.gfix (F : HTy → HTy) : HTy := ⟨fun n => (HTy.iter F (n + 1)).Q n⟩

theorem HTy.gfix_ap {F : HTy → HTy} (hF : Contractive F) :
    ∀ n, (HTy.gfix F).ap n = (HTy.iter F n).ap n
  | 0 => rfl
  | n + 1 => by
      show ((HTy.gfix F).ap n, (HTy.gfix F).Q n) =
        ((HTy.iter F (n + 1)).ap n, (HTy.iter F (n + 1)).Q n)
      rw [HTy.gfix_ap hF n, HTy.iter_stable hF n]; rfl

/-- **`gfix F` unfolds**: `F (gfix F)` has its predicates. -/
theorem HTy.gfix_unfold {F : HTy → HTy} (hF : Contractive F) :
    (HTy.gfix F).Q = (F (HTy.gfix F)).Q := by
  funext n
  have h : (F (HTy.gfix F)).ap (n + 1) = (HTy.iter F (n + 1)).ap (n + 1) :=
    hF _ _ n (HTy.gfix_ap hF n)
  have := HTy.Q_eq_of_ap h (Nat.lt_succ_self n)
  rw [this]; rfl

/-- **A guarded fixed point is lawful** when `F` gives a lawful type at every type. -/
theorem HTy.gfix_lawful {F : HTy → HTy} (hF : Contractive F) (hL : ∀ τ, (F τ).Lawful) :
    (HTy.gfix F).Lawful :=
  HTy.Lawful.of_Q_eq (HTy.gfix_unfold hF).symm (hL _)

/-! ### Instances at every depth -/

/-- `μX. Mut @a (thunk X)`: a cell holding a task that returns such a cell, at every depth. -/
def cellTask (a : Life) : HTy := HTy.gfix (fun X => HTy.mut a (HTy.thunk X))

theorem cellTask_contr (a : Life) : Contractive (fun X => HTy.mut a (HTy.thunk X)) :=
  (HTy.mut_contr a).comp_left HTy.thunk_contr.nonexp

theorem cellTask_lawful (a : Life) : (cellTask a).Lawful :=
  HTy.gfix_lawful (cellTask_contr a) fun _ => HTy.mut_lawful a _

theorem cellTask_unfold (a : Life) :
    (cellTask a).Q = (HTy.mut a (HTy.thunk (cellTask a))).Q :=
  HTy.gfix_unfold (cellTask_contr a)

/-- Depth 1: a cell holding a thunk. -/
def depth1 (a : Life) (Φ : HTy) : HTy := HTy.mut a (HTy.thunk Φ)

/-- Depth 3: a cell of tasks of cells of tasks of cells. -/
def depth3 (a b c : Life) (Φ : HTy) : HTy :=
  HTy.mut a (HTy.thunk (HTy.mut b (HTy.thunk (HTy.mut c (HTy.thunk Φ)))))

theorem depth1_lawful (a : Life) (Φ : HTy) : (depth1 a Φ).Lawful := HTy.mut_lawful _ _
theorem depth3_lawful (a b c : Life) (Φ : HTy) : (depth3 a b c Φ).Lawful := HTy.mut_lawful _ _

end BoCa.Fig16.Tree.HoStore

end
