import Core.Chain.Hardest791N
import Core.Chain.SI.TabLeN
import Core.Chain.SI.StopRaiseN

/-!
# #791 at the rule level over the chain relation: the interpretation and the statements
`[spec §62]`

`docs/new-core/scope-791-rule.md` is the plan. `Core/TreeGoal791.lean` states #791's end goal
over the tree relation; here the interpretation and the statements are restated over Core's
step-indexed chain relation `erwp` (`Core/Chain/SI/*`).

* **§1. The interpretation.** `vN A δ k v ρ` (`𝒱⟦A⟧δ` at the index `k`) and
  `cN C δ Φ k ls e ρ` (`𝒞⟦C⟧δ` at the location family `Φ`, the index `k` and the record list
  `ls`), with `F_Σ R` read at the table of the row's layers (`tabN`, each capturable entry with
  its cancel row's obligation `finN`) and its answer `retN`. Core's `vCE`/`cC`/`effTab`/`finObl`/
  `effRet` clause by clause, with `ewpTS`/`wpTS` replaced by `erwp`, as `SI/Sem.lean` does for
  `ewp`; `Mut` is `SI/MutSemN.lean`'s `vMut`. `gN`, `SemJN`.
* **§2. Laws.** Downward closure of every piece; `vN`/`cN` read `δ` only at free variables
  (`vN_congr`); computations monotone along `LocFam.Ext`; `𝒱⟦A⟧` of an outliving `A` in the
  stratum (`vN_outlives`); `F_Σ R` as `erwp` at the row's table (`cN_effOf`).
* **§3. The statements**: `ConstN`, `ConstsN`, `FundamentalN`, `BridgeN`, `Goal791SchedN`, and
  `goal791Sched_of`: `Goal791SchedN` from `FundamentalN` and `ConstsN`.

Values read neither `Φ` nor the record list (`SI/MutSemN.lean`: the stratification, not a
recursive world, breaks the circularity of `Mut`), so they are monotone along both by their type.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 ctx791 vals791 jdgC)
open BoCa.BoLo (Heap Kont hndE hndVal)

/-! ## §1. The interpretation -/

/-- An entry of a row's table: the qualifier; abortive as Core's (`B` empty, not `lin`); payload
and answer at their value types, at every record list; the cancel obligation where Core's `capB`
reads one; resumed under `extF`. -/
def entN (q : Qual) (B : VTy) (PA PB : Nat → Val → WRes → Prop)
    (fin : Option (Nat → List SRec → Expr → WProp)) : OpEntN where
  q := q
  abort := B.isZero && q != .lin
  PA := fun k _ v ρ => PA k v ρ
  PB := fun k _ v ρ => PB k v ρ
  fin := if capB q B then fin else none
  wc := extF

/-- One more layer of a table: the first match wins. -/
def extTabN (n i : UInt32) (en : OpEntN) (T : OpTabN) : OpTabN :=
  fun m j => if m = n ∧ j = i then some en else T m j

/-- **A `mut` borrow at `α` of the family `P`** (`vMut`, `SI/MutSemN.lean`): a location whose
`mut` cell at `α` holds the member `j ≥ n` of `P`. -/
def mutCell (α : Life) (P : Nat → Val → WRes → Prop) (n : Nat) (v : Val) (ρ : WRes) : Prop :=
  ∃ (l : Loc) (w : Val) (χ : WRes) (hχ : χ.InStratum α) (j : Nat) (hw : P j w χ), n ≤ j ∧
    v = Val.loc l ∧ ρ = ResU.single l (CellU.mutOf α w χ hχ (fun u r => P j u r.1) hw)

/-- **An `imm` borrow at `α`** (`ptoImmS`, `Core/Relation.lean`, without the record list): one
`imm` cell `imm(β̄, u, σ)` with `α ⊑ ⊓β̄` whose payload is in `P`. -/
def immCell (α : Life) (P : Val → WRes → Prop) (v : Val) (ρ : WRes) : Prop :=
  ∃ (l : Loc) (s : LSet) (u : Val) (σ : WRes) (h : σ.InStratum s.join), v = Val.loc l ∧
    ρ = ResU.single l (CellU.immOf s u σ h) ∧ α ⊑ s.meet ∧ P u σ

mutual
/-- **`𝒱⟦A⟧δ` at the index.** Core's `vCE` clause by clause, `⋆` written as `ResU.CompS`; `Mut`
is `vMut` (a location whose `mut` cell at `@aδ` holds the member `j ≥ k` of the payload's family);
`Imm` one `imm` cell longer-lived than `@aδ` with its payload in `𝒱⟦A⟧`; `[@a] A` in the
stratum; `U C` the forced thunk in `𝒞⟦C⟧` at every downward-closed `Φ` and every record list. A
lifetime with no interpretation reads as empty. Type variables, `μ`, families and opaque host
types are outside the fragment and empty. -/
def vN : VTy → LSub → Nat → Val → WRes → Prop
  | .unit, _, _, v, ρ => v = Val.unit ∧ ρ = PMap.empty
  | .tensor A B, δ, n, v, ρ => ∃ v₁ v₂ ρ₁ ρ₂, v = Val.pair v₁ v₂ ∧ ResU.CompS ρ₁ ρ₂ ρ ∧
      vN A δ n v₁ ρ₁ ∧ vN B δ n v₂ ρ₂
  | .zero, _, _, _, _ => False
  | .sum A B, δ, n, v, ρ =>
      (∃ v₁, v = Val.inj₁ v₁ ∧ vN A δ n v₁ ρ) ∨ (∃ v₂, v = Val.inj₂ v₂ ∧ vN B δ n v₂ ρ)
  | .thunk C, δ, n, v, ρ => ∀ Φ : LocFam, Φ.Down → ∀ ls, cN C δ Φ n ls (forceE C v.1) ρ
  | .ref A, δ, n, v, ρ => ∃ (l : Loc) (u : Val) (σ : WRes), v = Val.loc l ∧
      ResU.CompS (ResU.single l (CellU.ownOf u)) σ ρ ∧ vN A δ n u σ
  | .imm a A, δ, n, v, ρ => ∃ α, a.interp δ = some α ∧
      immCell α (fun u σ => vN A δ n u σ) v ρ
  | .mut a A, δ, n, v, ρ => ∃ α, a.interp δ = some α ∧
      mutCell α (fun j u r => vN A δ j u r) n v ρ
  | .box a A, δ, n, v, ρ => ∃ α, a.interp δ = some α ∧ vN A δ n v ρ ∧ ρ.InStratum α
  | .bang A, δ, n, v, ρ => ρ = PMap.empty ∧ vN A δ n v ρ
  | .unk, _, _, _, ρ => ρ = PMap.empty
  | .int w, _, _, v, ρ => v.IsInt w ∧ ρ = PMap.empty
  | .tvar _, _, _, _, _ => False
  | .mu _, _, _, _, _ => False
  | .fam _, _, _, _, _ => False
  | .opq _, _, _, _, _ => False
/-- **`𝒞⟦C⟧δ` at `Φ`, the index and the record list.** `F A` is `erwp` at the empty table;
`F_Σ R` is `erwp` at the table of the row's layers; `⊸` reads its argument at every later index
(the step-indexed `−∗`); `∀'x ⊏ @c` every `α ⊏ @cδ`, empty where `@c` has no interpretation;
`ν` is outside the fragment. -/
def cN : CTy → LSub → LocFam → Nat → List SRec → Expr → WRes → Prop
  | .ret A, δ, Φ, n, ls, e, ρ =>
      erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) (fun k _ v ρ => vN A δ k v ρ) n ls e ρ
  | .arr A C, δ, Φ, n, ls, e, ρ => ∀ k, k ≤ n → ∀ (v : Val) (ρv ρ' : WRes),
      ResU.CompS ρ ρv ρ' → vN A δ k v ρv → cN C δ Φ k ls (.app e (.val v)) ρ'
  | .amp C D, δ, Φ, n, ls, e, ρ => cN C δ Φ n ls (.app e (.val (Val.inj₁ .unit))) ρ ∧
      cN D δ Φ n ls (.app e (.val (Val.inj₂ .unit))) ρ
  | .top, _, _, _, _, _, _ => True
  | .all x c C, δ, Φ, n, ls, e, ρ => (∃ γ, c.interp δ = some γ) ∧
      ∀ α, LtLife δ c α → cN C (δ.extend x α) Φ n ls (.app e (.val .unit)) ρ
  | .nu _, _, _, _, _, _, _ => False
  | .eff m i q A B fin _ C, δ, Φ, n, ls, e, ρ =>
      erwp (ℍ := ℍ) Φ (opTableN (extTabN m i
          (entN q B (fun k v ρ => vN A δ k v ρ) (fun k v ρ => vN B δ k v ρ) (finN fin δ Φ))
          (tabN C δ Φ)))
        (fun k _ v ρ => retN C δ k v ρ) n ls e ρ
/-- The table of a row's layers below the top one. -/
def tabN : CTy → LSub → LocFam → OpTabN
  | .eff m i q A B fin _ C, δ, Φ => extTabN m i
      (entN q B (fun k v ρ => vN A δ k v ρ) (fun k v ρ => vN B δ k v ρ) (finN fin δ Φ))
      (tabN C δ Φ)
  | _, _, _ => OpTabN.empty
/-- **The cancel obligation of a cancel row**: `none` at `⊤`; otherwise the cancel run at the
table of the row's layers, read at `Φ`. -/
def finN : CTy → LSub → LocFam → Option (Nat → List SRec → Expr → WProp)
  | .top, _, _ => none
  | .eff m i q A B fin _ C, δ, Φ => some (cancelOblN (ℍ := ℍ) Φ (extTabN m i
      (entN q B (fun k v ρ => vN A δ k v ρ) (fun k v ρ => vN B δ k v ρ) (finN fin δ Φ))
      (tabN C δ Φ)))
  | .ret _, _, Φ => some (cancelOblN (ℍ := ℍ) Φ OpTabN.empty)
  | .arr _ _, _, Φ => some (cancelOblN (ℍ := ℍ) Φ OpTabN.empty)
  | .amp _ _, _, Φ => some (cancelOblN (ℍ := ℍ) Φ OpTabN.empty)
  | .all _ _ _, _, Φ => some (cancelOblN (ℍ := ℍ) Φ OpTabN.empty)
  | .nu _, _, Φ => some (cancelOblN (ℍ := ℍ) Φ OpTabN.empty)
/-- The answer of a row's layers. -/
def retN : CTy → LSub → Nat → Val → WRes → Prop
  | .ret A, δ, k, v, ρ => vN A δ k v ρ
  | .eff _ _ _ _ _ _ _ C, δ, k, v, ρ => retN C δ k v ρ
  | .arr _ _, _, _, _, _ => False
  | .amp _ _, _, _, _, _ => False
  | .top, _, _, _, _ => False
  | .all _ _ _, _, _, _, _ => False
  | .nu _, _, _, _, _ => False
end

/-- **`𝒢⟦Γ⟧δγ` at the index**: the live slots' values over a split of the resource. -/
def gN (δ : LSub) : Ctx VTy → List Val → Nat → WRes → Prop
  | [], _, _, ρ => ρ = PMap.empty
  | _ :: _, [], _, ρ => ρ = PMap.empty
  | s :: Γ, v :: γ, n, ρ => if s.live then
      ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ vN (ℍ := ℍ) s.ty δ n v ρ₁ ∧ gN δ Γ γ n ρ₂
    else gN δ Γ γ n ρ

/-- **`Δ; Γ ⊨ e : j` over `erwp`**: at every `δ ⊨ Δ`, every downward-closed location family,
index and record list, from every resource meeting the context. -/
def SemJN (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  ∀ (δ : LSub) (γ : List Val) (Φ : LocFam) (n : Nat) (ls : List SRec) (ρ : WRes),
    Δ.Models δ → Φ.Down → Ctx.LiveWithin Γ γ → gN (ℍ := ℍ) δ Γ γ n ρ →
      cN (ℍ := ℍ) (jdgC j) δ Φ n ls (substAll γ e) ρ

/-- **The table a task at the row `S` runs at**, at the location family `Φ`. -/
def rowTabN (S : Row) (Φ : LocFam) : OpTabN := tabN (ℍ := ℍ) (CTy.effOf S .unit) LSub.empty Φ

/-! ## §2. Laws -/

theorem extTabN_some {n i m j : UInt32} {en en' : OpEntN} {T : OpTabN}
    (h : extTabN n i en T m j = some en') : (m = n ∧ j = i ∧ en' = en) ∨ T m j = some en' := by
  unfold extTabN at h
  split at h
  · rename_i hmj; exact .inl ⟨hmj.1, hmj.2, (Option.some.inj h).symm⟩
  · exact .inr h

theorem extTabN_down {n i : UInt32} {q : Qual} {B : VTy} {PA PB : Nat → Val → WRes → Prop}
    {fin : Option (Nat → List SRec → Expr → WProp)} {T : OpTabN}
    (hA : ∀ k v ρ, PA (k + 1) v ρ → PA k v ρ)
    (hfin : ∀ P, fin = some P → ∀ k ls e ρ, P (k + 1) ls e ρ → P k ls e ρ) (hT : T.Down) :
    (extTabN n i (entN q B PA PB fin) T).Down where
  pa := fun m j en h k ls v ρ hp => by
    rcases extTabN_some h with ⟨-, -, rfl⟩ | h
    · exact hA k v ρ hp
    · exact hT.pa _ _ _ h k ls v ρ hp
  fin := fun m j en P h hP k ls e ρ hp => by
    rcases extTabN_some h with ⟨-, -, rfl⟩ | h
    · simp only [entN] at hP
      split at hP
      · exact hfin P hP k ls e ρ hp
      · cases hP
    · exact hT.fin _ _ _ _ h hP k ls e ρ hp
  wcl := fun m j en h => by
    rcases extTabN_some h with ⟨-, -, rfl⟩ | h
    · exact extF_left
    · exact hT.wcl _ _ _ h

theorem cancelOblN_down {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (hT : T.Down) :
    ∀ k ls e ρ, cancelOblN (ℍ := ℍ) Φ T (k + 1) ls e ρ → cancelOblN (ℍ := ℍ) Φ T k ls e ρ :=
  fun _ _ _ _ h => erwp_le hΦ (cancelTabN_local T) (cancelTabN_down hT) falsePost_down
    (Nat.le_succ _) h

mutual
theorem vN_down : ∀ (A : VTy) (δ : LSub) (n : Nat) (v : Val) (ρ : WRes),
    vN (ℍ := ℍ) A δ (n + 1) v ρ → vN (ℍ := ℍ) A δ n v ρ
  | .unit, _, _, _, _, h => h
  | .tensor A B, δ, n, _, _, h => by
      obtain ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, h₃, h₄⟩ := h
      exact ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, vN_down A δ n v₁ ρ₁ h₃, vN_down B δ n v₂ ρ₂ h₄⟩
  | .zero, _, _, _, _, h => h
  | .sum A B, δ, n, _, ρ, h => by
      rcases h with ⟨v₁, h₁, h₂⟩ | ⟨v₂, h₁, h₂⟩
      · exact .inl ⟨v₁, h₁, vN_down A δ n v₁ ρ h₂⟩
      · exact .inr ⟨v₂, h₁, vN_down B δ n v₂ ρ h₂⟩
  | .thunk C, δ, n, v, ρ, h => fun Φ hΦ ls => cN_down C δ Φ hΦ n ls _ ρ (h Φ hΦ ls)
  | .ref A, δ, n, _, _, h => by
      obtain ⟨l, u, σ, h₁, h₂, h₃⟩ := h
      exact ⟨l, u, σ, h₁, h₂, vN_down A δ n u σ h₃⟩
  | .imm a A, δ, n, _, _, h => by
      obtain ⟨α, hα, l, s, u, σ, hs, h₁, h₂, h₃, h₄⟩ := h
      exact ⟨α, hα, l, s, u, σ, hs, h₁, h₂, h₃, vN_down A δ n u σ h₄⟩
  | .mut a A, δ, n, _, _, h => by
      obtain ⟨α, hα, l, w, χ, hχ, j, hw, hj, h₁, h₂⟩ := h
      exact ⟨α, hα, l, w, χ, hχ, j, hw, by omega, h₁, h₂⟩
  | .box a A, δ, n, v, ρ, h => by
      obtain ⟨α, hα, h₁, h₂⟩ := h
      exact ⟨α, hα, vN_down A δ n v ρ h₁, h₂⟩
  | .bang A, δ, n, v, ρ, h => ⟨h.1, vN_down A δ n v ρ h.2⟩
  | .unk, _, _, _, _, h => h
  | .int _, _, _, _, _, h => h
  | .tvar _, _, _, _, _, h => h
  | .mu _, _, _, _, _, h => h
  | .fam _, _, _, _, _, h => h
  | .opq _, _, _, _, _, h => h
theorem cN_down : ∀ (C : CTy) (δ : LSub) (Φ : LocFam), Φ.Down → ∀ (n : Nat) (ls : List SRec)
    (e : Expr) (ρ : WRes), cN (ℍ := ℍ) C δ Φ (n + 1) ls e ρ → cN (ℍ := ℍ) C δ Φ n ls e ρ
  | .ret A, δ, Φ, hΦ, n, ls, e, ρ, h =>
      erwp_le hΦ (opTableN_local _) (opTableN_down OpTabN.empty_down)
        (fun k _ v ρ h => vN_down A δ k v ρ h) (Nat.le_succ n) h
  | .arr A C, δ, Φ, hΦ, n, ls, e, ρ, h => fun k hk => h k (by omega)
  | .amp C D, δ, Φ, hΦ, n, ls, e, ρ, h =>
      ⟨cN_down C δ Φ hΦ n ls _ ρ h.1, cN_down D δ Φ hΦ n ls _ ρ h.2⟩
  | .top, _, _, _, _, _, _, _, h => h
  | .all x c C, δ, Φ, hΦ, n, ls, e, ρ, h =>
      ⟨h.1, fun α hα => cN_down C (δ.extend x α) Φ hΦ n ls _ ρ (h.2 α hα)⟩
  | .nu _, _, _, _, _, _, _, _, h => h
  | .eff m i q A B fin rc C, δ, Φ, hΦ, n, ls, e, ρ, h =>
      erwp_le hΦ (opTableN_local _)
        (opTableN_down (extTabN_down (fun k v ρ h => vN_down A δ k v ρ h)
          (finN_down fin δ Φ hΦ) (tabN_down C δ Φ hΦ)))
        (fun k _ v ρ h => retN_down C δ k v ρ h) (Nat.le_succ n) h
theorem tabN_down : ∀ (C : CTy) (δ : LSub) (Φ : LocFam), Φ.Down → (tabN (ℍ := ℍ) C δ Φ).Down
  | .eff m i q A B fin rc C, δ, Φ, hΦ =>
      extTabN_down (fun k v ρ h => vN_down A δ k v ρ h) (finN_down fin δ Φ hΦ) (tabN_down C δ Φ hΦ)
  | .ret _, _, _, _ => OpTabN.empty_down
  | .arr _ _, _, _, _ => OpTabN.empty_down
  | .amp _ _, _, _, _ => OpTabN.empty_down
  | .top, _, _, _ => OpTabN.empty_down
  | .all _ _ _, _, _, _ => OpTabN.empty_down
  | .nu _, _, _, _ => OpTabN.empty_down
theorem finN_down : ∀ (F : CTy) (δ : LSub) (Φ : LocFam), Φ.Down →
    ∀ P, finN (ℍ := ℍ) F δ Φ = some P → ∀ k ls e ρ, P (k + 1) ls e ρ → P k ls e ρ
  | .top, _, _, _, _, h => by cases h
  | .eff m i q A B fin rc C, δ, Φ, hΦ, P, h => by
      simp only [finN, Option.some.injEq] at h
      subst h
      exact cancelOblN_down hΦ (extTabN_down (fun k v ρ h => vN_down A δ k v ρ h)
        (finN_down fin δ Φ hΦ) (tabN_down C δ Φ hΦ))
  | .ret _, _, Φ, hΦ, P, h => by
      simp only [finN, Option.some.injEq] at h; subst h
      exact cancelOblN_down hΦ OpTabN.empty_down
  | .arr _ _, _, Φ, hΦ, P, h => by
      simp only [finN, Option.some.injEq] at h; subst h
      exact cancelOblN_down hΦ OpTabN.empty_down
  | .amp _ _, _, Φ, hΦ, P, h => by
      simp only [finN, Option.some.injEq] at h; subst h
      exact cancelOblN_down hΦ OpTabN.empty_down
  | .all _ _ _, _, Φ, hΦ, P, h => by
      simp only [finN, Option.some.injEq] at h; subst h
      exact cancelOblN_down hΦ OpTabN.empty_down
  | .nu _, _, Φ, hΦ, P, h => by
      simp only [finN, Option.some.injEq] at h; subst h
      exact cancelOblN_down hΦ OpTabN.empty_down
theorem retN_down : ∀ (C : CTy) (δ : LSub) (n : Nat) (v : Val) (ρ : WRes),
    retN (ℍ := ℍ) C δ (n + 1) v ρ → retN (ℍ := ℍ) C δ n v ρ
  | .ret A, δ, n, v, ρ, h => vN_down A δ n v ρ h
  | .eff _ _ _ _ _ _ _ C, δ, n, v, ρ, h => retN_down C δ n v ρ h
  | .arr _ _, _, _, _, _, h => h
  | .amp _ _, _, _, _, _, h => h
  | .top, _, _, _, _, h => h
  | .all _ _ _, _, _, _, _, h => h
  | .nu _, _, _, _, _, h => h
end

theorem vN_le {A : VTy} {δ : LSub} {k n : Nat} (hkn : k ≤ n) {v : Val} {ρ : WRes}
    (h : vN (ℍ := ℍ) A δ n v ρ) : vN (ℍ := ℍ) A δ k v ρ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  clear hkn
  induction d with
  | zero => exact h
  | succ d ihd => exact ihd (vN_down A δ _ v ρ (by rwa [← Nat.add_assoc] at h))

theorem cN_le {C : CTy} {δ : LSub} {Φ : LocFam} (hΦ : Φ.Down) {k n : Nat} (hkn : k ≤ n)
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : cN (ℍ := ℍ) C δ Φ n ls e ρ) :
    cN (ℍ := ℍ) C δ Φ k ls e ρ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  clear hkn
  induction d with
  | zero => exact h
  | succ d ihd => exact ihd (cN_down C δ Φ hΦ _ ls e ρ (by rwa [← Nat.add_assoc] at h))

/-- A `Mut` payload's family is downward closed. -/
theorem vN_fam_down (A : VTy) (δ : LSub) (α : Life) :
    DownFam α (fun j u (r : ResS Loc Val α) => vN (ℍ := ℍ) A δ j u r.1) :=
  fun k u r h => vN_down A δ k u r.1 h

/-! ### Rows -/

/-- A row's answer is its base's value type. -/
theorem retN_effOf (S : Row) (R : VTy) (δ : LSub) :
    retN (ℍ := ℍ) (CTy.effOf S R) δ = vN (ℍ := ℍ) R δ := by
  induction S with
  | nil => funext k v ρ; simp only [CTy.effOf, retN]
  | cons o S ih => funext k v ρ; simp only [CTy.effOf, retN]; rw [ih]

/-- **`F_Σ R` is `erwp` at the row's table and `𝒱⟦R⟧`.** -/
theorem cN_effOf (S : Row) (R : VTy) (δ : LSub) (Φ : LocFam) (n : Nat) (ls : List SRec)
    (e : Expr) (ρ : WRes) :
    cN (ℍ := ℍ) (CTy.effOf S R) δ Φ n ls e ρ ↔
      erwp (ℍ := ℍ) Φ (opTableN (tabN (ℍ := ℍ) (CTy.effOf S R) δ Φ))
        (fun k _ v ρ => vN (ℍ := ℍ) R δ k v ρ) n ls e ρ := by
  cases S with
  | nil => simp only [CTy.effOf, cN, tabN]
  | cons o S =>
      simp only [CTy.effOf, cN, tabN]
      rw [retN_effOf]

/-! ### `δ` is read only at free variables -/

mutual
theorem vN_congr : ∀ (A : VTy) {δ δ' : LSub}, (∀ y, VFree y A → δ.find? y = δ'.find? y) →
    vN (ℍ := ℍ) A δ = vN (ℍ := ℍ) A δ'
  | .unit, _, _, _ => rfl
  | .tensor A B, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy))
      have h₂ := vN_congr B (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      funext n v ρ; simp only [vN, h₁, h₂]
  | .zero, _, _, _ => rfl
  | .sum A B, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy))
      have h₂ := vN_congr B (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      funext n v ρ; simp only [vN, h₁, h₂]
  | .thunk C, δ, δ', h => by
      have h₁ := cN_congr C (δ := δ) (δ' := δ') h
      funext n v ρ; simp only [vN, h₁]
  | .ref A, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') h
      funext n v ρ; simp only [vN, h₁]
  | .imm a A, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      funext n v ρ; simp only [vN, h₁, ha]
  | .mut a A, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      funext n v ρ; simp only [vN, ha]; rw [h₁]
  | .box a A, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      funext n v ρ; simp only [vN, h₁, ha]
  | .bang A, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') h
      funext n v ρ; simp only [vN, h₁]
  | .unk, _, _, _ => rfl
  | .int _, _, _, _ => rfl
  | .tvar _, _, _, _ => rfl
  | .mu _, _, _, _ => rfl
  | .fam _, _, _, _ => rfl
  | .opq _, _, _, _ => rfl
theorem cN_congr : ∀ (C : CTy) {δ δ' : LSub}, (∀ y, CFree y C → δ.find? y = δ'.find? y) →
    cN (ℍ := ℍ) C δ = cN (ℍ := ℍ) C δ'
  | .ret A, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') h
      funext Φ n ls e ρ; simp only [cN, h₁]
  | .arr A C, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy))
      have h₂ := cN_congr C (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      funext Φ n ls e ρ; simp only [cN, h₁, h₂]
  | .amp C D, δ, δ', h => by
      have h₁ := cN_congr C (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy))
      have h₂ := cN_congr D (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      funext Φ n ls e ρ; simp only [cN, h₁, h₂]
  | .top, _, _, _ => rfl
  | .all x c C, δ, δ', h => by
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') c (fun y hy => h y (.inl hy))
      have h₁ : ∀ α : Life, cN (ℍ := ℍ) C (δ.extend x α) = cN (ℍ := ℍ) C (δ'.extend x α) := by
        intro α
        refine cN_congr C (fun y hy => ?_)
        by_cases hxy : x = y
        · subst hxy
          rw [BoCa.Fig16.LogRel.find?_extend_self, BoCa.Fig16.LogRel.find?_extend_self]
        · rw [BoCa.Fig16.LogRel.find?_extend_ne _ _ hxy, BoCa.Fig16.LogRel.find?_extend_ne _ _ hxy]
          exact h y (.inr ⟨fun e => hxy e.symm, hy⟩)
      have hL : ∀ α : Life, LtLife δ c α = LtLife δ' c α := by
        intro α; unfold LtLife; rw [ha]
      funext Φ n ls e ρ; simp only [cN, h₁, hL, ha]
  | .nu _, _, _, _ => rfl
  | .eff m i q A B fin rc C, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy))
      have h₂ := vN_congr B (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inl hy)))
      have h₃ := finN_congr fin (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inl hy))))
      have h₄ := tabN_congr C (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inr hy))))
      have h₅ := retN_congr C (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inr hy))))
      funext Φ n ls e ρ; simp only [cN, h₁, h₂, h₃, h₄, h₅]
theorem tabN_congr : ∀ (C : CTy) {δ δ' : LSub}, (∀ y, CFree y C → δ.find? y = δ'.find? y) →
    tabN (ℍ := ℍ) C δ = tabN (ℍ := ℍ) C δ'
  | .eff m i q A B fin rc C, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy))
      have h₂ := vN_congr B (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inl hy)))
      have h₃ := finN_congr fin (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inl hy))))
      have h₄ := tabN_congr C (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inr hy))))
      funext Φ; simp only [tabN, h₁, h₂, h₃, h₄]
  | .ret _, _, _, _ => rfl
  | .arr _ _, _, _, _ => rfl
  | .amp _ _, _, _, _ => rfl
  | .top, _, _, _ => rfl
  | .all _ _ _, _, _, _ => rfl
  | .nu _, _, _, _ => rfl
theorem finN_congr : ∀ (F : CTy) {δ δ' : LSub}, (∀ y, CFree y F → δ.find? y = δ'.find? y) →
    finN (ℍ := ℍ) F δ = finN (ℍ := ℍ) F δ'
  | .eff m i q A B fin rc C, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy))
      have h₂ := vN_congr B (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inl hy)))
      have h₃ := finN_congr fin (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inl hy))))
      have h₄ := tabN_congr C (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inr hy))))
      funext Φ; simp only [finN, h₁, h₂, h₃, h₄]
  | .ret _, _, _, _ => rfl
  | .arr _ _, _, _, _ => rfl
  | .amp _ _, _, _, _ => rfl
  | .top, _, _, _ => rfl
  | .all _ _ _, _, _, _ => rfl
  | .nu _, _, _, _ => rfl
theorem retN_congr : ∀ (C : CTy) {δ δ' : LSub}, (∀ y, CFree y C → δ.find? y = δ'.find? y) →
    retN (ℍ := ℍ) C δ = retN (ℍ := ℍ) C δ'
  | .ret A, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') h
      funext n v ρ; simp only [retN, h₁]
  | .eff _ _ _ _ _ _ _ C, δ, δ', h => by
      have h₁ := retN_congr C (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inr hy))))
      funext n v ρ; simp only [retN, h₁]
  | .arr _ _, _, _, _ => rfl
  | .amp _ _, _, _, _ => rfl
  | .top, _, _, _ => rfl
  | .all _ _ _, _, _, _ => rfl
  | .nu _, _, _, _ => rfl
end

/-- Extending `δ` at a variable `A` does not mention leaves `𝒱⟦A⟧` alone. -/
theorem vN_extend_of_not_free {x : LifeVar} {A : VTy} (h : ¬ VFree x A) (δ : LSub) (α : Life) :
    vN (ℍ := ℍ) A (δ.extend x α) = vN (ℍ := ℍ) A δ :=
  vN_congr A fun y hy => BoCa.Fig16.LogRel.find?_extend_ne δ α (fun e => by subst e; exact h hy)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
