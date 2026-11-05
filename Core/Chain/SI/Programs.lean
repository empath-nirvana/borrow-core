import Core.Chain.SI.Loop
import Core.Chain.SI.Adequacy

/-!
# Stage 1: a file closed by an effectful finaliser, a scheduler that stores `κ`, a loop with no
bound, under the runtime's `Div` handler — `OrDiverges`, with no fuel

    prog cl = hnd_Div rtH (                       -- the runtime: every tick answered next
                hnd_Fs fsH (                       -- close : I32 ↠^lin 1, resumed at once
                  hnd_Y (cl) (                     -- the scheduler; y : 1 ↠^cancel 1
                    c ← alloc 1;                   -- the file
                    ubind (λ_. close_file c, λ_. close_file c)
                      (iterate (λs. λb. case b {next → y (); inr () | close → ()}, ()))))) 

`close_file c = (λn. close n) (free c)`: the finaliser releases the cell and performs `close`,
handled outside the scheduler. The scheduler's clause `cl` is one of

* `clStore`: `λ(v, κ). (λc. (free c).1 ()) (alloc κ)` — store `κ` in a cell, take it back, resume;
* `clCancel`:  `λ(v, κ). (λc. (free c).2) (alloc κ)` — store `κ`, take it back, cancel it.

The body loops for ever: the runtime answers every tick *next*. Under `clStore` the run never
ends; under `clCancel` the first `y`'s `κ` is cancelled, the cancel reaches the `ubind` frame, the
finaliser closes the file, and the run ends at the empty memory. `OrDiverges` holds of both.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Stage1
open BoCa
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  ubindE ccatchE kappaC errVal clauseAt capTag)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-! ### The operations' entries -/

/-- `tick : 1 ↠^lin Next`. -/
def tickS : OpSpec := ⟨fun _ v σ => v = Val.unit ∧ σ = emp,
  fun _ w σ => (w = nextV ∨ w = closeV) ∧ σ = emp, none⟩

/-- `close : I32 ↠^lin 1`, the descriptor's value as its argument. -/
def closeS : OpSpec := ⟨fun _ _ σ => σ = emp, fun _ w σ => w = Val.unit ∧ σ = emp, none⟩

/-- The finalisers' row `{close}`. -/
def rowD : UInt32 → UInt32 → Option OpSpec := fun m i => if m = 4 ∧ i = 0 then some closeS else none

/-- `y : 1 ↠^cancel 1`, whose cancel row is `{close}`. -/
def yS : OpSpec := ⟨fun _ v σ => v = Val.unit ∧ σ = emp, fun _ w σ => w = Val.unit ∧ σ = emp,
  some (cancelObl (ℍ := ℍ) rowD)⟩

/-- A protocol from its three entries, each present or not. -/
def prot3 (t c y : Bool) : Prot :=
  ⟨fun m i =>
    if m = divEff ∧ i = 0 then (if t then some tickS else none)
    else if m = 4 ∧ i = 0 then (if c then some closeS else none)
    else if m = 6 ∧ i = 0 then (if y then some (yS (ℍ := ℍ)) else none)
    else none,
   fun _ _ => none⟩

theorem divEff_ne4 : divEff ≠ 4 := by decide
theorem divEff_ne6 : divEff ≠ 6 := by decide

/-- The entries of `prot3`. -/
theorem prot3_perf {t c y : Bool} {m i : UInt32} {s : OpSpec} :
    (prot3 (ℍ := ℍ) t c y).perf m i = some s ↔
      (m = divEff ∧ i = 0 ∧ t = true ∧ s = tickS) ∨ (m = 4 ∧ i = 0 ∧ c = true ∧ s = closeS) ∨
      (m = 6 ∧ i = 0 ∧ y = true ∧ s = yS (ℍ := ℍ)) := by
  simp only [prot3]
  by_cases h₁ : m = divEff ∧ i = 0
  · obtain ⟨rfl, rfl⟩ := h₁
    simp only [and_self, if_true, divEff_ne4, divEff_ne6, false_and, or_false, true_and]
    cases t <;> simp [eq_comm]
  · rw [if_neg h₁]
    by_cases h₂ : m = 4 ∧ i = 0
    · obtain ⟨rfl, rfl⟩ := h₂
      simp only [and_self, if_true]
      cases c <;> simp [eq_comm, divEff_ne4]
    · rw [if_neg h₂]
      by_cases h₃ : m = 6 ∧ i = 0
      · obtain ⟨rfl, rfl⟩ := h₃
        simp only [and_self, if_true]
        cases y <;> simp [eq_comm, divEff_ne6]
      · rw [if_neg h₃]
        simp only [reduceCtorEq, false_iff]
        rintro (⟨h, h', -⟩ | ⟨h, h', -⟩ | ⟨h, h', -⟩)
        · exact h₁ ⟨h, h'⟩
        · exact h₂ ⟨h, h'⟩
        · exact h₃ ⟨h, h'⟩

theorem rowD_lin : LinRow rowD where
  lin := fun m i s h => by
    simp only [rowD] at h; split at h
    · cases h; rfl
    · cases h
  pa := fun m i s h n v σ hp => by
    simp only [rowD] at h; split at h
    · cases h; exact hp
    · cases h

theorem prot3_down (t c y : Bool) : (prot3 (ℍ := ℍ) t c y).Down where
  pa := fun m i s h n v σ hp => by
    rcases prot3_perf.1 h with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;> exact hp
  canc := fun m i s C h hc n e σ hC => by
    rcases prot3_perf.1 h with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩
    · cases hc
    · cases hc
    · cases hc; exact cancelObl_down rowD_lin hC
  rais := fun _ _ _ h => by cases h

/-! ### Clauses that resume at once -/

/-- `λ(v, κ). κ.1 w`. -/
def resumeCl (w : Val) : Val :=
  Val.lam (.letpair (.var 0) (.app (.app (.var 0) (.val (Val.inj₁ .unit))) (.val w)))

/-- `κ` as a value. -/
def kapV (hc : Bool) (ℓ : Loc) (H : Val) (K : Kont) : Val := ⟨kappaC hc ℓ H K, IsVal.lam⟩

theorem resumeCl_steps {P : Prot} {Q : Post} {w v : Val} (hw : closedAt 0 w.1 = true)
    {hc : Bool} {ℓ : Loc} {H : Val} {K : Kont} {n : Nat} {σ : Heap}
    (h : ewp (ℍ := ℍ) P Q n (.app (.app (kappaC hc ℓ H K) (.val (Val.inj₁ .unit))) (.val w)) σ) :
    ewp (ℍ := ℍ) P Q (n + 2) (.app (.val (resumeCl w)) (.pair (.val v) (kappaC hc ℓ H K))) σ := by
  have e₀ : (.app (.val (resumeCl w)) (.pair (.val v) (kappaC hc ℓ H K)) : Expr) =
      Kont.hole.plug (.app (.val (resumeCl w)) (.val (Val.pair v (kapV hc ℓ H K)))) := rfl
  rw [e₀]
  refine ewp_head (fun μ => Head.beta μ _ _) rfl .hole ?_
  have e₁ : Expr.subst 0 (Val.pair v (kapV hc ℓ H K))
      (.letpair (.var 0) (.app (.app (.var 0) (.val (Val.inj₁ .unit))) (.val w))) =
      Kont.hole.plug (.letpair (.val (Val.pair v (kapV hc ℓ H K)))
        (.app (.app (.var 0) (.val (Val.inj₁ .unit))) (.val w))) := by
    simp [Kont.plug, Expr.subst, subst_closedAt _ _ hw (Nat.zero_le _), Val.inj₁, Val.unit]
  rw [Kont.plug_hole, e₁]
  refine ewp_head (fun μ => Head.letpair μ _ _ _) rfl .hole ?_
  have e₂ : Expr.subst 0 v (Expr.subst 0 ((kapV hc ℓ H K).shift 1 0)
      (.app (.app (.var 0) (.val (Val.inj₁ .unit))) (.val w))) =
      Kont.hole.plug (.app (.app (kappaC hc ℓ H K) (.val (Val.inj₁ .unit))) (.val w)) := by
    simp only [Expr.subst, if_true, Val.val_shift, Kont.plug]
    rw [Expr.subst_shift 0 0 0 v _ le_rfl le_rfl, Expr.shift_zero,
      subst_closedAt _ _ hw (Nat.zero_le _), subst_closedAt _ _ hw (Nat.zero_le _)]
    rfl
  rw [e₂]
  exact h


/-! ### The postconditions -/

/-- Owning nothing: the postcondition of every scope here. -/
def QE : Post := fun _ _ σ => σ = emp

theorem QE_down : QE.Down := fun _ _ _ h => h

theorem protNone_down : Prot.none.Down where
  pa := fun _ _ _ h => by cases h
  canc := fun _ _ _ _ h => by cases h
  rais := fun _ _ _ h => by cases h

/-- `λx. x`. -/
def idV : Val := Val.lam (.var 0)

theorem idV_ret {P : Prot} {k : Nat} {v : Val} {σ : Heap} (h : σ = emp) :
    ewp (ℍ := ℍ) P QE k (.app (.val idV) (.val v)) σ := by
  refine ewp_pred fun k₁ _ => ?_
  have := ewp_head (ℍ := ℍ) (P := P) (Q := QE) (n := k₁) (σ := σ)
    (fun μ => Head.beta μ (.var 0) v) rfl .hole
  simp only [Kont.plug_hole, Expr.subst, if_true] at this
  exact this (ewp_val (v := v) h)

theorem clauseAt_pair0 (c r : Val) : clauseAt (Val.pair c r).1 0 = some c := by
  simp [clauseAt, Val.pair, c.2]

theorem capTag_one (q : Qual) : capTag (qualsVal [q]).1 (0 : UInt32).toNat = q.tag :=
  capTag_qualsVal [q] 0 (by simp)

/-- A clause that resumes at once, `λ(v, κ). κ.1 w`, given `KSpec` at an answer `w ∈ PB` owning
nothing. -/
theorem resumeCl_ok {P : Prot} {Q : Post} (hP : P.Down) (hQ : Q.Down) {w : Val}
    (hw : closedAt 0 w.1 = true) {H : Val} {s : OpSpec} (hb : ∀ j, s.PB j w emp)
    {k : Nat} {v : Val} {ℓ : Loc} {K : Kont} {σk : Heap} (hℓ : σk ℓ = none) (hc : Bool)
    (hK : KSpec (ℍ := ℍ) H s P Q k K σk) :
    ewp (ℍ := ℍ) P Q k (.app (.val (resumeCl w)) (.pair (.val v) (kappaC hc ℓ H K)))
      (un emp (un (single ℓ Val.unit) σk)) := by
  rw [un_emp_left]
  have h₀ := hK.1 (k - 8) (by omega) w emp (disj_emp_right σk) (hb _)
  rw [un_emp_right] at h₀
  exact ewp_le hP hQ (by omega) (resumeCl_steps hw (ewp_resume hℓ h₀))

/-! ### The runtime's handler of `Div` -/

theorem rtC_eq : DivRuntime.rtC = resumeCl nextV := rfl

theorem rt_spec : HSpec (ℍ := ℍ) divEff (qualsVal [.lin]) DivRuntime.rtR (Val.pair DivRuntime.rtC .unit)
    (prot3 (ℍ := ℍ) true false false) Prot.none QE QE where
  ret := fun _ _ _ h => idV_ret h
  fwd := fun m i s hm h => by
    rcases prot3_perf.1 h with ⟨h₁, -⟩ | ⟨-, -, h₂, -⟩ | ⟨-, -, h₂, -⟩
    · exact absurd h₁ hm
    · cases h₂
    · cases h₂
  rfwd := fun _ _ _ h => by cases h
  clause := fun i s h => by
    rcases prot3_perf.1 h with ⟨-, rfl, -, rfl⟩ | ⟨h₁, -⟩ | ⟨h₁, -⟩
    · refine ⟨DivRuntime.rtC, .lin, clauseAt_pair0 _ _, capTag_one _, by decide, ?_⟩
      rintro k v σa ℓ K σk - hℓ ⟨-, rfl⟩ hK
      rw [rtC_eq]
      exact resumeCl_ok (s := tickS) protNone_down QE_down rfl (fun _ => ⟨.inl rfl, rfl⟩) hℓ _ hK
    · exact absurd h₁ divEff_ne4
    · exact absurd h₁ divEff_ne6

/-! ### `with_fs`: the handler of `close` -/

def fsH : Val := hndVal 4 (qualsVal [.lin]) idV (Val.pair (resumeCl Val.unit) .unit)

theorem fs_spec : HSpec (ℍ := ℍ) 4 (qualsVal [.lin]) idV (Val.pair (resumeCl Val.unit) .unit)
    (prot3 (ℍ := ℍ) true true false) (prot3 (ℍ := ℍ) true false false) QE QE where
  ret := fun _ _ _ h => idV_ret h
  fwd := fun m i s hm h => by
    rcases prot3_perf.1 h with ⟨h₁, h₂, -, rfl⟩ | ⟨h₁, -⟩ | ⟨-, -, h₂, -⟩
    · exact prot3_perf.2 (.inl ⟨h₁, h₂, rfl, rfl⟩)
    · exact absurd h₁ hm
    · cases h₂
  rfwd := fun _ _ _ h => by cases h
  clause := fun i s h => by
    rcases prot3_perf.1 h with ⟨h₁, -⟩ | ⟨-, rfl, -, rfl⟩ | ⟨h₁, -⟩
    · exact absurd h₁.symm divEff_ne4
    · refine ⟨resumeCl Val.unit, .lin, clauseAt_pair0 _ _, capTag_one _, by decide, ?_⟩
      rintro k v σa ℓ K σk - hℓ rfl hK
      exact resumeCl_ok (s := closeS) (prot3_down _ _ _) QE_down rfl (fun _ => ⟨rfl, rfl⟩) hℓ _ hK
    · cases h₁

/-! ### The scheduler: store `κ` in a cell, take it back, then resume it or cancel it -/

/-- `λ(v, κ). (λc. B) (alloc κ)`. -/
def storeCl (B : Expr) : Val :=
  Val.lam (.letpair (.var 0) (.app (.val (Val.lam B)) (.app (.val (.prim .alloc)) (.var 0))))

/-- Resume: `B = (free c).1 ()`. -/
def clStore : Val := storeCl (.app (.app (freeE (.var 0)) (.val (Val.inj₁ .unit))) (.val .unit))

/-- Cancel: `B = (free c).2`. -/
def clCancel : Val := storeCl (.app (freeE (.var 0)) (.val (Val.inj₂ .unit)))

/-- **Storing `κ`**: the clause's first four steps put `κ` in a fresh cell `ℓ′`, owned. -/
theorem storeCl_steps {P : Prot} {Q : Post} {B : Expr} (hB : closedAt 1 B = true) {v κ : Val}
    {n : Nat} {σ : Heap}
    (h : ∀ ℓ', σ ℓ' = none →
      ewp (ℍ := ℍ) P Q n (B.subst 0 (Val.loc ℓ')) (un (single ℓ' κ) σ)) :
    ewp (ℍ := ℍ) P Q (n + 4) (.app (.val (storeCl B)) (.pair (.val v) (.val κ))) σ := by
  have e₀ : (.app (.val (storeCl B)) (.pair (.val v) (.val κ)) : Expr) =
      Kont.hole.plug (.app (.val (storeCl B)) (.val (Val.pair v κ))) := rfl
  rw [e₀]
  refine ewp_head (fun μ => Head.beta μ _ _) rfl .hole ?_
  have e₁ : Expr.subst 0 (Val.pair v κ)
      (.letpair (.var 0) (.app (.val (Val.lam B)) (.app (.val (.prim .alloc)) (.var 0)))) =
      Kont.hole.plug (.letpair (.val (Val.pair v κ))
        (.app (.val (Val.lam B)) (.app (.val (.prim .alloc)) (.var 0)))) := by
    simp [Kont.plug, Expr.subst, subst_closedAt _ _ hB (by omega : 1 ≤ 3), Val.lam]
  rw [Kont.plug_hole, e₁]
  refine ewp_head (fun μ => Head.letpair μ _ _ _) rfl .hole ?_
  have e₂ : Expr.subst 0 v (Expr.subst 0 (κ.shift 1 0)
      (.app (.val (Val.lam B)) (.app (.val (.prim .alloc)) (.var 0)))) =
      (Kont.appR (.val (Val.lam B)) .hole).plug (.app (.val (.prim .alloc)) (.val κ)) := by
    simp only [Expr.subst, if_true, Val.val_shift, Kont.plug, Val.val_lam]
    rw [Expr.subst_shift 0 0 0 v _ le_rfl le_rfl, Expr.shift_zero,
      subst_closedAt _ _ hB (by omega : 1 ≤ 1), subst_closedAt _ _ hB (by omega : 1 ≤ 1)]
    rfl
  rw [Kont.plug_hole, e₂]
  refine ewp_alloc _ _ fun ℓ' hℓ' => ?_
  refine ewp_head (fun μ => Head.beta μ _ _) rfl .hole ?_
  exact h ℓ' hℓ'

theorem cancelObl_le {k n : Nat} (hkn : k ≤ n) {x : Expr} {σ : Heap}
    (h : cancelObl (ℍ := ℍ) rowD n x σ) : cancelObl (ℍ := ℍ) rowD k x σ :=
  ewp_le (cancelProt_down rowD_lin) (fun _ _ _ h => h) hkn h

def yH (cl : Val) : Val := hndVal 6 (qualsVal [.cancel]) idV (Val.pair cl .unit)

/-- The clause `clStore` meets its obligation: eleven steps to `hnd H K[()]`. -/
theorem clStore_ok {k : Nat} {v : Val} {ℓ : Loc} {K : Kont} {σk : Heap} (hℓ : σk ℓ = none)
    (hK : KSpec (ℍ := ℍ) (yH clStore) (yS (ℍ := ℍ)) (prot3 (ℍ := ℍ) true true false) QE k K σk) :
    ewp (ℍ := ℍ) (prot3 (ℍ := ℍ) true true false) QE k
      (.app (.val clStore) (.pair (.val v) (kappaC true ℓ (yH clStore) K)))
      (un emp (un (single ℓ Val.unit) σk)) := by
  rw [un_emp_left]
  have h₀ := hK.1 (k - 11) (by omega) Val.unit emp (disj_emp_right σk) ⟨rfl, rfl⟩
  rw [un_emp_right] at h₀
  have h₁ := ewp_resume (hc := true) (ℓ := ℓ) hℓ h₀
  refine ewp_le (prot3_down _ _ _) QE_down (by omega)
    (storeCl_steps (B := .app (.app (freeE (.var 0)) (.val (Val.inj₁ .unit))) (.val .unit)) rfl
      (v := v) (κ := kapV true ℓ (yH clStore) K) (n := k - 11 + 7) fun ℓ' hℓ' => ?_)
  have e : Expr.subst 0 (Val.loc ℓ')
      (.app (.app (freeE (.var 0)) (.val (Val.inj₁ .unit))) (.val .unit)) =
      (Kont.appL (Kont.appL .hole (Val.inj₁ .unit)) .unit).plug (freeE (.val (Val.loc ℓ'))) := by
    simp [Expr.subst, Kont.plug, freeE, Val.inj₁, Val.unit, Val.loc]
  rw [e]
  exact ewp_free _ hℓ' h₁

/-- The clause `clCancel` meets its obligation: ten steps to `κ`'s cancel run, which the
operation's cancel obligation covers. -/
theorem clCancel_ok {k : Nat} {v : Val} {ℓ : Loc} {K : Kont} {σk : Heap} (hℓ : σk ℓ = none)
    (hK : KSpec (ℍ := ℍ) (yH clCancel) (yS (ℍ := ℍ)) (prot3 (ℍ := ℍ) true true false) QE k K σk) :
    ewp (ℍ := ℍ) (prot3 (ℍ := ℍ) true true false) QE k
      (.app (.val clCancel) (.pair (.val v) (kappaC true ℓ (yH clCancel) K)))
      (un emp (un (single ℓ Val.unit) σk)) := by
  rw [un_emp_left]
  have hc := hK.2 _ rfl
  have h₀ : ewp (ℍ := ℍ) (prot3 (ℍ := ℍ) true true false) QE (k - 10)
      (ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))) σk :=
    ewp_ccatch (Pc := rowD) (fun m i s h => by
        simp only [rowD] at h
        split at h
        · rename_i hmi; cases h; exact prot3_perf.2 (.inr (.inl ⟨hmi.1, hmi.2, rfl, rfl⟩))
        · cases h)
      (fun _ => rfl) _ _ _ (cancelObl_le (by omega) hc)
  have h₁ := ewp_cancelK (ℓ := ℓ) (H := yH clCancel) hℓ h₀
  refine ewp_le (prot3_down _ _ _) QE_down (by omega)
    (storeCl_steps (B := .app (freeE (.var 0)) (.val (Val.inj₂ .unit))) rfl
      (v := v) (κ := kapV true ℓ (yH clCancel) K) (n := k - 10 + 6) fun ℓ' hℓ' => ?_)
  have e : Expr.subst 0 (Val.loc ℓ') (.app (freeE (.var 0)) (.val (Val.inj₂ .unit))) =
      (Kont.appL .hole (Val.inj₂ .unit)).plug (freeE (.val (Val.loc ℓ'))) := by
    simp [Expr.subst, Kont.plug, freeE, Val.inj₂, Val.unit, Val.loc]
  rw [e]
  exact ewp_free _ hℓ' h₁

/-- **The scheduler's specification**, at either clause. -/
theorem y_spec (cl : Val) (hcl : cl = clStore ∨ cl = clCancel) :
    HSpec (ℍ := ℍ) 6 (qualsVal [.cancel]) idV (Val.pair cl .unit)
      (prot3 (ℍ := ℍ) true true true) (prot3 (ℍ := ℍ) true true false) QE QE where
  ret := fun _ _ _ h => idV_ret h
  fwd := fun m i s hm h => by
    rcases prot3_perf.1 h with ⟨h₁, h₂, -, rfl⟩ | ⟨h₁, h₂, -, rfl⟩ | ⟨h₁, -⟩
    · exact prot3_perf.2 (.inl ⟨h₁, h₂, rfl, rfl⟩)
    · exact prot3_perf.2 (.inr (.inl ⟨h₁, h₂, rfl, rfl⟩))
    · exact absurd h₁ hm
  rfwd := fun _ _ _ h => by cases h
  clause := fun i s h => by
    rcases prot3_perf.1 h with ⟨h₁, -⟩ | ⟨h₁, -⟩ | ⟨-, rfl, -, rfl⟩
    · exact absurd h₁.symm divEff_ne6
    · cases h₁
    · refine ⟨cl, .cancel, clauseAt_pair0 _ _, capTag_one _, by decide, ?_⟩
      rintro k v σa ℓ K σk - hℓ ⟨-, rfl⟩ hK
      rcases hcl with rfl | rfl
      · exact clStore_ok hℓ hK
      · exact clCancel_ok hℓ hK

/-! ### The file and its finaliser -/

/-- `close_file ℓ = (λn. close n) (free ℓ)`, the finaliser's body at the file `ℓ`. -/
def closeFile (c : Expr) : Expr :=
  .app (.val (Val.lam (.app (.val (.prim .perform))
    (.pair (.val (Val.i32 4)) (.pair (.val (Val.i32 0)) (.var 0)))))) (freeE c)

/-- `λ_. close_file ℓ`: both the finaliser and the normal exit. -/
def closeFin (ℓ : Loc) : Val := Val.lam (closeFile (.val (Val.loc ℓ)))

/-- **The finaliser**, owning the file, releases it, performs `close`, and answers `()` owning
nothing. -/
theorem closeFin_ok {P : Prot} {Q : Post} (hc : P.perf 4 0 = some closeS) (hQ : ∀ k, Q k Val.unit emp)
    (ℓ : Loc) (u w : Val) (k : Nat) :
    ewp (ℍ := ℍ) P Q k (.app (.val (closeFin ℓ)) (.val w)) (single ℓ u) := by
  refine ewp_pred fun k₁ _ => ?_
  refine ewp_head (K := .hole) (fun μ => Head.beta μ _ w) rfl ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 w (closeFile (.val (Val.loc ℓ)))) =
      (Kont.appR (.val (Val.lam (.app (.val (.prim .perform))
        (.pair (.val (Val.i32 4)) (.pair (.val (Val.i32 0)) (.var 0)))))) .hole).plug
        (freeE (.val (Val.loc ℓ))) := by
    simp [closeFile, Expr.subst, Kont.plug, freeE, Val.lam, Val.i32, Val.loc, Expr.val]
  rw [e₁, ← un_emp_right (single ℓ u)]
  refine ewp_pred fun k₂ _ => ?_
  refine ewp_free _ rfl ?_
  refine ewp_pred fun k₃ _ => ?_
  refine ewp_head (K := .hole) (fun μ => Head.beta μ _ u) rfl ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 u (.app (.val (.prim .perform))
      (.pair (.val (Val.i32 4)) (.pair (.val (Val.i32 0)) (.var 0))))) =
      Kont.hole.plug (performE (.val (opPayload 4 0 u))) := by
    simp [Expr.subst, performE, opPayload, Val.pair, Val.i32, Expr.val]
  rw [e₂, ← un_emp_left emp]
  refine ewp_pred fun k₄ _ => ?_
  refine ewp_perform _ rfl hc (disj_emp_left emp) rfl ?_ (fun C h => by cases h)
  rintro j - w' σw - ⟨rfl, rfl⟩
  exact ewp_val (hQ j)

/-! ### The loop -/

/-- `y ()`. -/
def yE : Expr := performE (.val (opPayload 6 0 Val.unit))

/-- The step `λs. λb. case b {next → y (); inr () | close → ()}`. -/
def fL : Val := Val.lam (.lam (.case (.var 0) (.seq yE (.inj₂ (.val .unit))) (.val .unit)))

/-- The loop's protocol: `tick` and `y`. -/
abbrev PL : Prot := prot3 (ℍ := ℍ) true false true

theorem PL_ctxClosed : CtxClosed (PL (ℍ := ℍ)) := by
  intro m i s C h hc K hH hC k x σ hx
  rcases prot3_perf.1 h with ⟨-, -, -, rfl⟩ | ⟨-, -, h₂, -⟩ | ⟨-, -, -, rfl⟩
  · cases hc
  · cases h₂
  · cases hc
    exact cancelObl_ctx rowD_lin hH hC k x σ hx

/-- The loop's invariant: the state is `()`, owning nothing — the file is the frame's. -/
def IL : Val → Heap → Prop := fun s σ => s = Val.unit ∧ σ = emp

theorem turn_ok (k : Nat) :
    ewp (ℍ := ℍ) PL (turnPost IL QE) k (.app (.app (.val fL) (.val Val.unit)) (.val nextV)) emp := by
  refine ewp_pred fun k₁ _ => ?_
  refine ewp_head (K := .appL .hole nextV) (fun μ => Head.beta μ _ Val.unit) rfl ?_
  refine ewp_pred fun k₂ _ => ?_
  have e₁ : (Kont.appL .hole nextV).plug (Expr.subst 0 Val.unit
      (.lam (.case (.var 0) (.seq yE (.inj₂ (.val .unit))) (.val .unit)))) =
      Kont.hole.plug (.app (.val (Val.lam (.case (.var 0) (.seq yE (.inj₂ (.val .unit)))
        (.val .unit)))) (.val nextV)) := by
    simp [Expr.subst, Kont.plug, yE, performE, opPayload, Val.pair, Val.i32, Val.unit, Val.lam,
      Expr.val]
  rw [e₁]
  refine ewp_head (fun μ => Head.beta μ _ nextV) rfl .hole ?_
  refine ewp_pred fun k₃ _ => ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 nextV
      (.case (.var 0) (.seq yE (.inj₂ (.val .unit))) (.val .unit))) =
      Kont.hole.plug (.case (.val (Val.inj₁ Val.unit)) (.seq yE (.inj₂ (.val .unit)))
        (.val .unit)) := by
    simp [Expr.subst, Kont.plug, yE, performE, opPayload, Val.pair, Val.i32, Val.unit, nextV,
      Val.inj₁, Expr.val]
  rw [e₂]
  refine ewp_head (fun μ => Head.case₁ μ Val.unit _ _) rfl .hole ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 Val.unit (.seq yE (.inj₂ (.val .unit)))) =
      (Kont.seq .hole (.inj₂ (.val .unit))).plug (performE (.val (opPayload 6 0 Val.unit))) := by
    simp [Expr.subst, Kont.plug, yE, performE, opPayload, Val.pair, Val.i32, Val.unit, Expr.val]
  rw [e₃, ← un_emp_left emp]
  refine ewp_pred fun k₄ _ => ?_
  refine ewp_perform _ rfl (prot3_perf.2 (.inr (.inr ⟨rfl, rfl, rfl, rfl⟩))) (disj_emp_left emp)
    ⟨rfl, rfl⟩ ?_ ?_
  · rintro j - w σw - ⟨rfl, rfl⟩
    rw [un_emp_left]
    refine ewp_pred fun j₁ _ => ?_
    refine ewp_head (K := .hole) (fun μ => Head.seq μ _) rfl ?_
    exact ewp_val (v := Val.inj₂ Val.unit) (.inr ⟨Val.unit, rfl, rfl, rfl⟩)
  · intro C hC
    cases hC
    refine ewp_pred fun j₁ _ => ?_
    exact ewp_raise (K := .seq .hole (.inj₂ (.val .unit))) rfl rfl ⟨rfl, rfl⟩

theorem close_ok (k : Nat) :
    ewp (ℍ := ℍ) PL QE k
      (.app (.val inrV) (.app (.app (.val fL) (.val Val.unit)) (.val closeV))) emp := by
  refine ewp_pred fun k₁ _ => ?_
  refine ewp_head (K := .appR (.val inrV) (.appL .hole closeV))
    (fun μ => Head.beta μ _ Val.unit) rfl ?_
  refine ewp_pred fun k₂ _ => ?_
  have e₁ : (Kont.appR (.val inrV) (.appL .hole closeV)).plug (Expr.subst 0 Val.unit
      (.lam (.case (.var 0) (.seq yE (.inj₂ (.val .unit))) (.val .unit)))) =
      (Kont.appR (.val inrV) .hole).plug (.app (.val (Val.lam (.case (.var 0)
        (.seq yE (.inj₂ (.val .unit))) (.val .unit)))) (.val closeV)) := by
    simp [Expr.subst, Kont.plug, yE, performE, opPayload, Val.pair, Val.i32, Val.unit, Val.lam,
      Expr.val]
  rw [e₁]
  refine ewp_head (fun μ => Head.beta μ _ closeV) rfl _ ?_
  refine ewp_pred fun k₃ _ => ?_
  have e₂ : (Kont.appR (.val inrV) .hole).plug (Expr.subst 0 closeV
      (.case (.var 0) (.seq yE (.inj₂ (.val .unit))) (.val .unit))) =
      (Kont.appR (.val inrV) .hole).plug (.case (.val (Val.inj₂ Val.unit))
        (.seq yE (.inj₂ (.val .unit))) (.val .unit)) := by
    simp [Expr.subst, Kont.plug, yE, performE, opPayload, Val.pair, Val.i32, Val.unit, closeV,
      Val.inj₂, Expr.val]
  rw [e₂]
  refine ewp_head (fun μ => Head.case₂ μ Val.unit _ _) rfl _ ?_
  refine ewp_pred fun k₄ _ => ?_
  have e₃ : (Kont.appR (.val inrV) .hole).plug (Expr.subst 0 Val.unit (.val Val.unit)) =
      Kont.hole.plug (.app (.val inrV) (.val Val.unit)) := by
    simp [Expr.subst, Kont.plug, Val.unit, Expr.val]
  rw [e₃]
  refine ewp_head (fun μ => Head.beta μ _ Val.unit) rfl .hole ?_
  exact ewp_val (v := Val.inj₂ Val.unit) rfl

/-- `iterate (fL, ())`. -/
def loopE : Expr := iterateE fL Val.unit

/-- **The loop is in `ewp` at every index**: it never ends while the ticks are answered *next*. -/
theorem loop_ok (n : Nat) : ewp (ℍ := ℍ) PL QE n loopE emp :=
  ewp_iterate (I := IL) (ts := tickS) rfl PL_ctxClosed QE_down
    (prot3_perf.2 (.inl ⟨rfl, rfl, rfl, rfl⟩)) rfl (fun _ => ⟨rfl, rfl⟩) (fun _ _ _ h => h)
    (by rintro s σ ⟨rfl, -⟩; rfl)
    (by rintro k s σ ⟨rfl, rfl⟩; exact turn_ok k)
    (by rintro k s σ ⟨rfl, rfl⟩; exact close_ok k) n Val.unit emp ⟨rfl, rfl⟩

/-! ### The body: open the file, loop, close it on every exit -/

/-- `λc. ubind (λ_. close_file c, λ_. close_file c) loop`. -/
def bodyF : Expr :=
  .app (.app (.val (.prim .ubind)) (.pair (.val (Val.lam (closeFile (.var 1))))
    (.val (Val.lam (closeFile (.var 1)))))) loopE

/-- `c ← alloc 1; ubind (…) loop`. -/
def body : Expr := .app (.val (Val.lam bodyF)) (.app (.val (.prim .alloc)) (.val (Val.i32 1)))

theorem bodyF_subst (ℓ : Loc) :
    Expr.subst 0 (Val.loc ℓ) bodyF = ubindE (Val.pair (closeFin ℓ) (closeFin ℓ)) loopE := by
  simp [bodyF, closeFin, closeFile, ubindE, Expr.subst, loopE, iterateE, fL, yE, performE, opPayload,
    Val.pair, Val.i32, Val.unit, Val.lam, Val.loc, freeE, Expr.val, Expr.shift]

/-- The finalisers' protocol: `close` alone. -/
abbrev PD : Prot := prot3 (ℍ := ℍ) false true false

theorem PD_fin : FinProt (PD (ℍ := ℍ)) where
  lin := fun m i s h => by
    rcases prot3_perf.1 h with ⟨-, -, h₂, -⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, h₂, -⟩
    · cases h₂
    · rfl
    · cases h₂
  rais := fun _ _ => rfl

theorem PD_le {t y : Bool} : ∀ m i s, (PD (ℍ := ℍ)).perf m i = some s →
    (prot3 (ℍ := ℍ) t true y).perf m i = some s := fun m i s h => by
  rcases prot3_perf.1 h with ⟨-, -, h₂, -⟩ | ⟨h₁, h₂, -, rfl⟩ | ⟨-, -, h₂, -⟩
  · cases h₂
  · exact prot3_perf.2 (.inr (.inl ⟨h₁, h₂, rfl, rfl⟩))
  · cases h₂

theorem PD_le_rowD : ∀ m i s, (PD (ℍ := ℍ)).perf m i = some s → rowD m i = some s :=
  fun m i s h => by
    rcases prot3_perf.1 h with ⟨-, -, h₂, -⟩ | ⟨rfl, rfl, -, rfl⟩ | ⟨-, -, h₂, -⟩
    · cases h₂
    · rfl
    · cases h₂

/-- **The body**, owning nothing: the file is allocated, held by the finaliser frame across the
loop, and the loop's `y`s carry the frame's finaliser in their cancel obligation. -/
theorem body_ok (n : Nat) : ewp (ℍ := ℍ) (prot3 (ℍ := ℍ) true true true) QE n body emp := by
  refine ewp_pred fun n₁ _ => ?_
  refine ewp_alloc (K := .appR (.val (Val.lam bodyF)) .hole) (Val.i32 1) fun ℓ _ => ?_
  refine ewp_pred fun n₂ _ => ?_
  refine ewp_head (K := .hole) (fun μ => Head.beta μ _ _) rfl ?_
  rw [Kont.plug_hole, bodyF_subst, un_emp_right, ← un_emp_left (single ℓ (Val.i32 1))]
  have hD : ∀ k, ewp (ℍ := ℍ) PD QD k (.app (.val (closeFin ℓ)) (.val Val.unit))
      (single ℓ (Val.i32 1)) :=
    fun k => closeFin_ok (prot3_perf.2 (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩))) (fun _ => ⟨rfl, rfl⟩) ℓ _ _ k
  refine ewp_ubind (Pin := PL) (Qin := QE) PD_fin PD_le ?_ hD ?_ (fun _ _ _ h => by cases h) n₂
    loopE emp (disj_emp_left _) (loop_ok n₂)
  · rintro k w σ - rfl
    rw [un_emp_left]
    exact closeFin_ok (prot3_perf.2 (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩))) (fun _ => rfl) ℓ _ _ k
  · intro m i s h
    rcases prot3_perf.1 h with ⟨h₁, h₂, -, rfl⟩ | ⟨-, -, h₂, -⟩ | ⟨h₁, h₂, -, rfl⟩
    · exact ⟨tickS, prot3_perf.2 (.inl ⟨h₁, h₂, rfl, rfl⟩), rfl, rfl, fun C' h' => by cases h'⟩
    · cases h₂
    · refine ⟨yS, prot3_perf.2 (.inr (.inr ⟨h₁, h₂, rfl, rfl⟩)), rfl, rfl, fun C' h' => ?_⟩
      cases h'
      exact ⟨_, rfl, cancelObl_ubind rowD_lin PD_fin PD_le_rowD hD⟩

/-! ### The programs, and `OrDiverges` -/

/-- `hnd_Div rtH (hnd_Fs fsH (hnd_Y cl body))`. -/
def prog (cl : Val) : Expr := hndE DivRuntime.rtH (hndE fsH (hndE (yH cl) body))

/-- Store `κ`, take it back, resume it: the run never ends. -/
def progStore : Expr := prog clStore

/-- Store `κ`, take it back, cancel it: the cancel closes the file and the run ends. -/
def progCancel : Expr := prog clCancel

theorem prog_ok (cl : Val) (hcl : cl = clStore ∨ cl = clCancel) (n : Nat) :
    ewp (ℍ := ℍ) Prot.none QE n (prog cl) emp :=
  ewp_handle rt_spec (prot3_down _ _ _) n _ _
    (ewp_handle fs_spec (prot3_down _ _ _) n _ _
      (ewp_handle (y_spec cl hcl) (prot3_down _ _ _) n _ _ (body_ok n)))

/-- **Stage 1, store and resume**: every configuration a run reaches is a value or steps, a value
only at the empty memory, and every `free` finds its cell. No fuel. -/
theorem progStore_orDiverges : OrDiverges (ℍ := ℍ) progStore :=
  adequacy (fun _ _ _ h => h) (prog_ok clStore (.inl rfl))

/-- **Stage 1, store and cancel**: the same, for the scheduler that cancels the stored `κ`. -/
theorem progCancel_orDiverges : OrDiverges (ℍ := ℍ) progCancel :=
  adequacy (fun _ _ _ h => h) (prog_ok clCancel (.inr rfl))

end BoCa.Fig16.LogRel.Core.Chain.SI.Stage1

end
