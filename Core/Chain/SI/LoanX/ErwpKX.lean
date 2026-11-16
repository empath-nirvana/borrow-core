import Core.Chain.SI.LoanX.LoanWorld
import Core.Chain.SI.LoanX.ErwpX
import Core.Chain.SI.LoanX.HandleX

/-!
# A world-indexed masked loan run

This is the recursive execution seam for a parked loan continuation. A segment
keeps its `LoanKW` fixed; a stop's table may owe its continuation at another
world admitted by `LoanKW.Owed`. The table and typed value clauses are
parameters here. No existing `cN` or `erwpK` judgment is changed.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont performE opPayload)

/-- A stop table can read the world and mask at capture and the world and mask
of every continuation it owes. -/
abbrev LoanTableX := LoanKW → Mask → Mask → Set Life → Nat → List SRec → Expr →
  (LoanKW → Mask → ContX) → XProp

/-- A value may be posted at a later typed world. The resource at that value
remains the complete physical/ghost resource. -/
def erwpKXPost (V : LoanKW → LoanKW → Prop) (x : LoanKW) (M : Mask)
    (Tb : LoanTableX) (Q : LoanKW → PostX) (Ψ : LoanKW → Mask → ContX) : PostGX :=
  fun M' C k ls t r =>
    (M' = M ∧ ∃ v : Val, t = v.1 ∧ ∃ y, V x y ∧ Q y C k ls v r) ∨
      Tb x M M' C k ls t Ψ r

/-- A world-indexed `erwpX`: ordinary steps use the fixed world's `LocFam`,
and only a stop can enter a different world. -/
def erwpKX (V : LoanKW → LoanKW → Prop) (Φ : LoanKW → LocFam)
    (Tb : LoanTableX) (Q : LoanKW → PostX) :
    LoanKW → Mask → Nat → List SRec → Expr → XProp
  | x, M, n, ls, e =>
      rwpGX (ℍ := ℍ) (Φ x) M
        (erwpKXPost V x M Tb Q (fun y M' k' ls' e' =>
          if _h : k' < n then erwpKX V Φ Tb Q y M' k' ls' e' else fun _ => False))
        n ls e
termination_by _ _ n => n

/-- The recursive obligation available below the enclosing step index. -/
def erwpKXC (V : LoanKW → LoanKW → Prop) (Φ : LoanKW → LocFam)
    (Tb : LoanTableX) (Q : LoanKW → PostX) (N : Nat) : LoanKW → Mask → ContX :=
  fun y M' k' ls' e' =>
    if k' < N then erwpKX (ℍ := ℍ) V Φ Tb Q y M' k' ls' e' else fun _ => False

theorem erwpKX_eq (V : LoanKW → LoanKW → Prop) (Φ : LoanKW → LocFam)
    (Tb : LoanTableX) (Q : LoanKW → PostX) (x : LoanKW) (M : Mask)
    (n : Nat) (ls : List SRec) (e : Expr) :
    erwpKX (ℍ := ℍ) V Φ Tb Q x M n ls e =
      rwpGX (ℍ := ℍ) (Φ x) M
        (erwpKXPost V x M Tb Q (erwpKXC (ℍ := ℍ) V Φ Tb Q n)) n ls e := by
  rw [erwpKX]
  congr 1

/-- A well-formed stop table observes recursive continuations only below the
stop index, including when it quantifies over future worlds. -/
def LoanTableX.Local (Tb : LoanTableX) : Prop :=
  ∀ x M M' C k ls t (Ψ Ψ' : LoanKW → Mask → ContX) r,
    (∀ y M'' k', k' < k → ∀ ls' e' r', Ψ y M'' k' ls' e' r' →
      Ψ' y M'' k' ls' e' r') →
    Tb x M M' C k ls t Ψ r → Tb x M M' C k ls t Ψ' r

theorem erwpKX_unfold_at {V : LoanKW → LoanKW → Prop}
    {Φ : LoanKW → LocFam} {Tb : LoanTableX} (hTb : Tb.Local)
    {Q : LoanKW → PostX} {x : LoanKW} {M : Mask} {n N : Nat}
    (hnN : n ≤ N) {ls : List SRec} {e : Expr} {r : XRes}
    (h : erwpKX (ℍ := ℍ) V Φ Tb Q x M n ls e r) :
    rwpGX (ℍ := ℍ) (Φ x) M
      (erwpKXPost V x M Tb Q (erwpKXC (ℍ := ℍ) V Φ Tb Q N)) n ls e r := by
  rw [erwpKX_eq] at h
  refine rwpGX_mono_le (fun M' C k hk ls' t r' ht => ?_) h
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hTb x M M' C k ls' t _ _ r' (fun y M'' k' hk' ls'' e'' r'' hΨ => ?_) ht)
    simp only [erwpKXC, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
    exact hΨ

/-- The table's world admission uses both main `KW.Owed` and registry validity
at the continuation's owned share. -/
def LoanTableX.OwesAt (x : LoanKW) (f : Life) (y : LoanKW)
    (share : XRes) : Prop := x.Owed f y share

/-- The answer predicate is read at the world where the parked continuation
resumes. A linear stop cannot discard its owned continuation cell. -/
structure LoanOpEntX where
  q : Qual
  remask : Bool
  PA : Nat → List SRec → Val → XProp
  PB : LoanKW → Nat → List SRec → Val → XProp
  wc : List SRec → List SRec → XRes → Prop

abbrev LoanOpTabX := UInt32 → UInt32 → Option LoanOpEntX

/-- The continuation's complete resource is the share used to test both
`KW.Owed` and registry validity at every future world. -/
def loanContShareX (x : LoanKW) (en : LoanOpEntX) (k : Nat)
    (ls : List SRec) (K : Kont) (Ψ : LoanKW → Mask → ContX)
    (M' : Mask) : XProp := fun share =>
  (en.q = .unr → share.1 = PMap.empty) ∧
  ∃ f, f ≤ x.typed.lo ∧
    ∀ y, x.Owed f y share → ∀ ls', en.wc ls ls' share →
      ∀ k', k' < k → ∀ w : Val,
        wandX (en.PB y k' ls' w) (Ψ y M' k' ls' (K.plug (.val w))) share

/-- A must-resume operation can park the continuation at `M'`. The captured
share is separated from the operation payload and is checked against the
same loan-world order at every admitted reply. -/
def loanPerformTableX (T : LoanOpTabX) : LoanTableX :=
  fun x M M' _ k ls t Ψ r =>
    ∃ (K : Kont) (n i : UInt32) (v : Val) (en : LoanOpEntX),
      t = K.plug (performE (.val (opPayload n i v))) ∧
      K.HasHnd n = false ∧ T n i = some en ∧
      (en.remask = true ∨ M' = M) ∧
      sepX (en.PA k ls v) (loanContShareX x en k ls K Ψ M') r

theorem loanPerformTableX_local (T : LoanOpTabX) :
    (loanPerformTableX T).Local := by
  rintro x M M' C k ls t Ψ Ψ' r hΨ
    ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, ρa, ρk, ga, gk, hc, hg, hA,
      hu, f, hf, hcont⟩
  exact ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, ρa, ρk, ga, gk, hc, hg, hA,
    hu, f, hf, fun y hy ls' hwc k' hk w z z' hB hz =>
      hΨ y M' k' hk _ _ _ ((hcont y hy ls' hwc k' hk w z z' hB hz))⟩

#print axioms erwpKX_eq
#print axioms erwpKX_unfold_at
#print axioms loanPerformTableX_local
end BoCa.Fig16.LogRel.Core.Chain.SI
