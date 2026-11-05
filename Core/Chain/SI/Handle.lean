import Core.Chain.SI.Ewp

/-!
# Step-indexed relation: deep handlers, and resuming or cancelling `κ`

**The handler rule** (`ewp_handle`). `hnd H e`, `H = (nm, (qs, (h_ret, hs)))`, is in `ewp` at the
outer protocol when `e` is at the inner one and `H` meets `HSpec`. The clause of an operation is
asked to be safe for every continuation `K` that meets `KSpec`: resumed at every answer, `hnd H
K[w]` is in the *outer* `ewp`; and cancelled, its region meets the operation's cancel obligation.
That is the deep handler's fixed point, and it is solved by the step index: the rule is proved by
induction on the index, and at a stop the continuation is in the inner `ewp` only at smaller
indices, where the induction hypothesis already puts `hnd H K[w]` in the outer one.

This is where `[TR]`-style total `ewpTS` (a least fixed point) and the `Div` row's `cwp` (a
greatest fixed point) could not meet: the clause may store `κ` and resume it any
number of steps later, into `ewp` at a later index, and no fixed point has to contain the object
being built. Nothing in the rule mentions `Div`: a body that ticks for ever passes its ticks
outward (`fwd`), each consuming an index.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  clauseAt capTag kappaC kappaAt kappaCBody ccatchE)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- What a continuation `K` captured by `hnd H` at the operation `s` owes, owning `σk`, at index
`k`: resumed at every answer in `s.PB` (at every `j ≤ k`), `hnd H K[w]` is in the outer `ewp`;
and if `s` may be cancelled, its cancelled region meets the obligation. -/
def KSpec (H : Val) (s : OpSpec) (P : Prot) (Q : Post) (k : Nat) (K : Kont) (σk : Heap) : Prop :=
  (∀ j, j ≤ k → ∀ w σw, Disj σk σw → s.PB j w σw →
    ewp (ℍ := ℍ) P Q j (hndE H (K.plug (.val w))) (un σk σw)) ∧
  (∀ C, s.cancel = some C → C k (K.dead.plug (raiseE (.val (cancelVal none)))) σk)

/-- **A handler's specification.** `h_ret` takes the inner postcondition to the outer `ewp` one
step later; operations of other names pass to the same entries of the outer protocol, raises to
weaker ones; no raise of `nm` is allowed inside (no abortive clause is used); and the clause of
each operation of `nm` the inner protocol has is safe, given its argument and a `κ` at a fresh
cell `ℓ` whose continuation meets `KSpec`. -/
structure HSpec (nm : UInt32) (qs hr hs : Val) (Pin Pout : Prot) (Qin Qout : Post) : Prop where
  ret : ∀ k v σ, Qin (k + 1) v σ → ewp (ℍ := ℍ) Pout Qout k (.app (.val hr) (.val v)) σ
  fwd : ∀ m i s, m ≠ nm → Pin.perf m i = some s → Pout.perf m i = some s
  rfwd : ∀ m i R, Pin.rais m i = some R →
    m ≠ nm ∧ ∃ R', Pout.rais m i = some R' ∧ ∀ k v σ, R k v σ → R' k v σ
  clause : ∀ i s, Pin.perf nm i = some s → ∃ (c : Val) (q : Qual),
    clauseAt hs.1 i.toNat = some c ∧ capTag qs.1 i.toNat = q.tag ∧ q ≠ .unr ∧
    ∀ k v σa ℓ K σk, Disj σa (un (single ℓ Val.unit) σk) → σk ℓ = none → s.PA k v σa →
      KSpec (ℍ := ℍ) (hndVal nm qs hr hs) s Pout Qout k K σk →
      ewp (ℍ := ℍ) Pout Qout k
        (.app (.val c) (.pair (.val v) (kappaC (cellCancel q) ℓ (hndVal nm qs hr hs) K)))
        (un σa (un (single ℓ Val.unit) σk))

section
variable {P : Prot} {Q : Post}

/-- **The catch**: `[op]`, the allocation of `κ`'s cell, and `κ`'s β-step, each its
configuration's only step but the allocation, which may take any location the memory misses. -/
theorem ewp_catch {n : Nat} {nm i : UInt32} {qs hr hs c v : Val} {K : Kont} {q : Qual}
    (hc : clauseAt hs.1 i.toNat = some c) (hK : K.HasHnd nm = false)
    (htag : capTag qs.1 i.toNat = q.tag) (hq : q ≠ .unr) {σ : Heap}
    (h : ∀ ℓ, σ ℓ = none → ∀ k, k + 3 ≤ n → ewp (ℍ := ℍ) P Q k
      (.app (.val c) (.pair (.val v) (kappaC (cellCancel q) ℓ (hndVal nm qs hr hs) K)))
      (un (single ℓ Val.unit) σ)) :
    ewp (ℍ := ℍ) P Q n (hndE (hndVal nm qs hr hs) (K.plug (performE (.val (opPayload nm i v)))))
      σ := by
  refine ewp_pred fun n₁ hn₁ => ?_
  have h₁ := fun μ => catch_step (ℍ := ℍ) (qs := qs) (hr := hr) μ v hc hK .hole
  simp only [Kont.plug_hole] at h₁
  refine ewp_det h₁ ?_
  have e₁ := plug_kappaCell .hole c v (cellCancel q) (hndVal nm qs hr hs) K
  simp only [Kont.plug_hole] at e₁
  rw [htag, kappaAt_cell hq, e₁]
  refine ewp_pred fun n₂ hn₂ => ?_
  refine ewp_alloc _ _ fun ℓ hℓ => ?_
  have e₂ := plug_kappaCellLoc .hole c v (cellCancel q) (hndVal nm qs hr hs) K ℓ
  simp only [Kont.plug_hole] at e₂
  rw [e₂]
  refine ewp_pred fun n₃ hn₃ => ?_
  have h₃ := fun μ => kappaCell_beta (ℍ := ℍ) μ .hole c v (cellCancel q) ℓ (hndVal nm qs hr hs) K
  simp only [Kont.plug_hole] at h₃ ⊢
  exact ewp_det h₃ (h ℓ hℓ n₃ (by omega))

/-- `PA` is downward closed over any number of indices. -/
theorem Prot.Down.pa_le (hP : P.Down) {m i : UInt32} {s : OpSpec} (hs : P.perf m i = some s)
    {k n : Nat} (hkn : k ≤ n) {v : Val} {σ : Heap} (h : s.PA n v σ) : s.PA k v σ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  clear hkn
  induction d with
  | zero => exact h
  | succ d ihd => exact ihd (hP.pa _ _ _ hs _ _ _ (by rwa [← Nat.add_assoc] at h))

theorem Prot.Down.canc_le (hP : P.Down) {m i : UInt32} {s : OpSpec} (hs : P.perf m i = some s)
    {C : Nat → Expr → Heap → Prop} (hc : s.cancel = some C)
    {k n : Nat} (hkn : k ≤ n) {e : Expr} {σ : Heap} (h : C n e σ) : C k e σ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  clear hkn
  induction d with
  | zero => exact h
  | succ d ihd => exact ihd (hP.canc _ _ _ _ hs hc _ _ _ (by rwa [← Nat.add_assoc] at h))

end

/-- **The deep handler rule.** -/
theorem ewp_handle {nm : UInt32} {qs hr hs : Val} {Pin Pout : Prot} {Qin Qout : Post}
    (hH : HSpec (ℍ := ℍ) nm qs hr hs Pin Pout Qin Qout) (hPin : Pin.Down) :
    ∀ n e σ, ewp (ℍ := ℍ) Pin Qin n e σ →
      ewp (ℍ := ℍ) Pout Qout n (hndE (hndVal nm qs hr hs) e) σ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro e σ h
  cases n with
  | zero => exact ewp_zero _ _
  | succ n =>
  rcases ewp_succ.1 h with ⟨v, rfl, hq⟩ | ⟨K, m, i, v, s, rfl, hK, hs', σa, σk, hd, rfl, hA, hB, hC⟩ |
    ⟨K, m, i, v, R, rfl, hK, hR, hRv⟩ | ⟨hnv, hst⟩
  · have h₁ := fun μ => catch_ret (ℍ := ℍ) μ nm qs hr hs v .hole
    simp only [Kont.plug_hole] at h₁
    exact ewp_det h₁ (hH.ret _ _ _ hq)
  · by_cases hm : m = nm
    · subst hm
      obtain ⟨c, q, hc, htag, hq, hcl⟩ := hH.clause i s hs'
      refine ewp_catch hc hK htag hq fun ℓ hℓ k hk => ?_
      obtain ⟨hℓa, hℓk⟩ := un_eq_none.1 hℓ
      have hdℓ : Disj (single ℓ Val.unit) σk := single_disj.2 hℓk
      rw [un_left_comm (single_disj.2 hℓa)]
      refine hcl k v σa ℓ K σk ?_ hℓk (hPin.pa_le hs' (by omega) hA) ⟨?_, ?_⟩
      · exact disj_un_right.2 ⟨disj_comm.1 (single_disj.2 hℓa), hd⟩
      · intro j hj w σw hw hb
        exact ih j (by omega) _ _ (hB j (by omega) w σw hw hb)
      · intro C hc'
        exact hPin.canc_le hs' hc' (by omega) (hC C hc')
    · have hs'' := hH.fwd m i s hm hs'
      have hplug : hndE (hndVal nm qs hr hs) (K.plug (performE (.val (opPayload m i v)))) =
          ((hndK (hndVal nm qs hr hs)).comp K).plug (performE (.val (opPayload m i v))) := by
        rw [Kont.plug_comp]; rfl
      rw [hplug]
      refine ewp_perform _ (by rw [hasHnd_comp, hndK_hasHnd, hK]; simpa using Ne.symm hm) hs'' hd hA
        ?_ ?_
      · intro k hk w σw hw hb
        rw [Kont.plug_comp]
        exact ih k (by omega) _ _ (hB k hk w σw hw hb)
      · intro C hc'
        rw [dead_comp, dead_hndK]
        simpa [Kont.comp] using hC C hc'
  · obtain ⟨hm, R', hR', hRR⟩ := hH.rfwd _ _ _ hR
    have hplug : hndE (hndVal nm qs hr hs) (K.plug (raiseE (.val (opPayload m i v)))) =
        ((hndK (hndVal nm qs hr hs)).comp K).plug (raiseE (.val (opPayload m i v))) := by
      rw [Kont.plug_comp]; rfl
    rw [hplug]
    exact ewp_raise _ (by rw [catches_comp, hndK_catches, hK]; simpa using Ne.symm hm) hR'
      (hRR _ _ _ hRv)
  · have e₁ : ∀ x, hndE (hndVal nm qs hr hs) x = (hndK (hndVal nm qs hr hs)).plug x := fun _ => rfl
    rw [e₁, ← un_emp_right σ]
    refine ewp_ctx_step _ (disj_emp_right σ) hnv hst fun e' σ' _ he' => ?_
    rw [un_emp_right, ← e₁]
    exact ih n (by omega) _ _ he'

/-! ### Using `κ` -/

section
variable {P : Prot} {Q : Post}

/-- **Resuming `κ`** at its cell: six steps, the release of the cell among them, to
`hnd H K[w]`. -/
theorem ewp_resume {n : Nat} {hc : Bool} {ℓ : Loc} {H : Val} {K : Kont} {w : Val} {σ : Heap}
    (hℓ : σ ℓ = none) (h : ewp (ℍ := ℍ) P Q n (hndE H (K.plug (.val w))) σ) :
    ewp (ℍ := ℍ) P Q (n + 6)
      (.app (.app (kappaC hc ℓ H K) (.val (Val.inj₁ .unit))) (.val w))
      (un (single ℓ Val.unit) σ) := by
  have h₁ := fun μ => kappaC_beta (ℍ := ℍ) μ hc ℓ H K (Val.inj₁ Val.unit) (.appL .hole w)
  refine ewp_det h₁ ?_
  have h₂ := fun μ => kappaC_case₁ (ℍ := ℍ) μ hc ℓ H K ((Val.inj₁ Val.unit).shift 1 0) Val.unit
    (.appL .hole w)
  refine ewp_det h₂ ?_
  have h₃ : (Kont.appL .hole w).plug (.seq (.val Val.unit) (.seq (freeE (.val (Val.loc ℓ)))
      (kResume H K).1)) = (Kont.appL .hole w).plug (.seq (.val Val.unit)
        (.seq (freeE (.val (Val.loc ℓ))) (kResume H K).1)) := rfl
  refine ewp_head (fun μ => Head.seq μ _) rfl (.appL .hole w) ?_
  have h₄ : (Kont.appL .hole w).plug (.seq (freeE (.val (Val.loc ℓ))) (kResume H K).1) =
      (Kont.appL (Kont.seq .hole (kResume H K).1) w).plug (freeE (.val (Val.loc ℓ))) := rfl
  rw [h₄]
  refine ewp_free _ hℓ ?_
  have h₅ : (Kont.appL (Kont.seq .hole (kResume H K).1) w).plug (.val Val.unit) =
      (Kont.appL .hole w).plug (.seq (.val Val.unit) (kResume H K).1) := rfl
  rw [h₅]
  refine ewp_head (fun μ => Head.seq μ _) rfl (.appL .hole w) ?_
  exact ewp_head (fun μ => kResume_beta μ H K w) rfl .hole h

/-- **Cancelling a cancellable `κ`** at its cell: five steps, the release of the cell among them,
to its cancel run `ccatch (K†[raise (0, (0, none))])`. -/
theorem ewp_cancelK {n : Nat} {ℓ : Loc} {H : Val} {K : Kont} {σ : Heap} (hℓ : σ ℓ = none)
    (h : ewp (ℍ := ℍ) P Q n (ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))) σ) :
    ewp (ℍ := ℍ) P Q (n + 5) (.app (kappaC true ℓ H K) (.val (Val.inj₂ .unit)))
      (un (single ℓ Val.unit) σ) := by
  have h₁ := fun μ => kappaC_beta (ℍ := ℍ) μ true ℓ H K (Val.inj₂ Val.unit) .hole
  simp only [Kont.plug_hole] at h₁
  refine ewp_det h₁ ?_
  have h₂ := fun μ => kappaC_case₂ (ℍ := ℍ) μ true ℓ H K ((Val.inj₂ Val.unit).shift 1 0) Val.unit
    .hole
  simp only [Kont.plug_hole] at h₂
  refine ewp_det h₂ ?_
  rw [subst_kCanBr_cancel]
  refine ewp_head (K := .hole) (fun μ => Head.seq μ _) rfl ?_
  have h₄ : Kont.hole.plug (.seq (freeE (.val (Val.loc ℓ)))
      (ccatchE (K.dead.plug (raiseE (.val (cancelVal none)))))) =
      (Kont.seq .hole (ccatchE (K.dead.plug (raiseE (.val (cancelVal none)))))).plug
        (freeE (.val (Val.loc ℓ))) := rfl
  rw [h₄]
  refine ewp_free _ hℓ ?_
  exact ewp_head (K := .hole) (fun μ => Head.seq μ _) rfl h

end

end BoCa.Fig16.LogRel.Core.Chain.SI

end
