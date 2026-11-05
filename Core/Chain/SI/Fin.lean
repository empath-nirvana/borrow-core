import Core.Chain.SI.Handle

/-!
# Step-indexed relation: finalisers, cancel runs, and `ccatch`

* `ewp_ubind`: `ubind (N, D) M` — `M` then `N`, with the finaliser `D` on every unwind — owning
  `M`'s fragment and `D`'s `σ_D`. `D` runs at a protocol of must-resume operations and never
  raises (the finalisers never fail, `[let-closeFin]`'s `¬ Σ_D.Cancels`), and consumes `σ_D`. On an
  ordinary raise `[finalise]` runs `D (); raise p`; on a cancel `[finalise-cancel]` runs
  `cfin s (D ())`, and the cancel goes on (`[cfin-ret]`). An operation `M` stops at passes the frame;
  its cancelled region now holds the frame, so the outer cancel obligation must follow from the
  inner one with `σ_D` added (`CancelExt`).
* `cancelProt`/`cancelObl`: the protocol of a cancel run and its obligation. The run performs only
  must-resume operations of its row and ends at the cancel's `raise (0, (0, none))`, under a context
  that catches nothing, owning nothing: every cell of the cancelled region has been released.
* `cancelObl_ubind`, `cancelObl_ctx`: the obligation is kept by a finaliser frame (which adds its
  `σ_D`) and by a context with no catcher (which adds nothing).
* `ewp_ccatch`: `κ`'s cancel branch `ccatch (K†[raise (0, (0, none))])` answers `()` owning nothing.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  ubindE ccatchE cfinE errVal)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- The finaliser frame `ubind (N, D) [·]`. -/
def ubK (N D : Val) : Kont := .appR (.app (.val (.prim .ubind)) (.val (Val.pair N D))) .hole

/-- The frame `cfin s [·]`. -/
def cfK (st : Val) : Kont := .appR (.app (.val (.prim .cfin)) (.val st)) .hole

/-- The frame `ccatch [·]`. -/
def ccK : Kont := .appR (.val (.prim .ccatch)) .hole

@[simp] theorem ubK_hasHnd (N D : Val) (m : UInt32) : (ubK N D).HasHnd m = false := by
  simp [ubK, Kont.HasHnd, Val.pair, Expr.val]

@[simp] theorem ubK_dead (N D : Val) : (ubK N D).dead = ubK N D := by
  simp [ubK, Kont.dead, Kont.DeadFrame, Val.pair, Expr.val]

@[simp] theorem cfK_hasHnd (st : Val) (m : UInt32) : (cfK st).HasHnd m = false := by
  simp [cfK, Kont.HasHnd, Expr.val]

@[simp] theorem ccK_hasHnd (m : UInt32) : ccK.HasHnd m = false := by
  simp [ccK, Kont.HasHnd, Expr.val, Val.prim]

@[simp] theorem ccK_dead : ccK.dead = .hole := by
  simp [ccK, Kont.dead, Kont.DeadFrame, Expr.val, Val.prim]

theorem ubK_plug (N D : Val) (e : Expr) : (ubK N D).plug e = ubindE (.pair N D) e := rfl
theorem cfK_plug (st : Val) (e : Expr) : (cfK st).plug e = cfinE st e := rfl
theorem ccK_plug (e : Expr) : ccK.plug e = ccatchE e := rfl

/-! ### Cancel runs -/

/-- The protocol of a cancel run whose operations are `Pc`'s: it may end at the cancel's raise,
with no error kept, owning nothing. -/
def cancelProt (Pc : UInt32 → UInt32 → Option OpSpec) : Prot :=
  ⟨Pc, fun m i => if m = 0 ∧ i = 0 then some (fun _ v σ => v = errVal none ∧ σ = emp) else none⟩

/-- **The cancel obligation** of an operation whose cancel row's operations are `Pc`. -/
def cancelObl (Pc : UInt32 → UInt32 → Option OpSpec) : Nat → Expr → Heap → Prop :=
  fun n x σ => ewp (ℍ := ℍ) (cancelProt Pc) (fun _ _ _ => False) n x σ

/-- A row of must-resume operations, whose arguments' predicates are downward closed. -/
structure LinRow (Pc : UInt32 → UInt32 → Option OpSpec) : Prop where
  lin : ∀ m i s, Pc m i = some s → s.cancel = none
  pa : ∀ m i s, Pc m i = some s → ∀ n v σ, s.PA (n + 1) v σ → s.PA n v σ

theorem cancelProt_down {Pc : UInt32 → UInt32 → Option OpSpec} (hc : LinRow Pc) :
    (cancelProt Pc).Down where
  pa := hc.pa
  canc := fun m i s C hs h => by rw [hc.lin m i s hs] at h; cases h
  rais := fun m i R h n v σ hr => by
    simp only [cancelProt] at h
    split at h
    · cases h; exact hr
    · cases h

theorem cancelObl_down {Pc : UInt32 → UInt32 → Option OpSpec} (hc : LinRow Pc) {n : Nat}
    {x : Expr} {σ : Heap} (h : cancelObl (ℍ := ℍ) Pc (n + 1) x σ) : cancelObl (ℍ := ℍ) Pc n x σ :=
  ewp_down (cancelProt_down hc) (fun _ _ _ h => h) n x σ h

/-! ### `ccatch` -/

/-- **`ccatch` around a cancel run** answers `()`, owning nothing; the run's operations pass it
to the same entries outside. -/
theorem ewp_ccatch {Pc : UInt32 → UInt32 → Option OpSpec} {P' : Prot} {Q' : Post}
    (hperf : ∀ m i s, Pc m i = some s → P'.perf m i = some s) (hQ' : ∀ k, Q' k Val.unit emp) :
    ∀ n x σ, cancelObl (ℍ := ℍ) Pc n x σ → ewp (ℍ := ℍ) P' Q' n (ccatchE x) σ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x σ h
  cases n with
  | zero => exact ewp_zero _ _
  | succ n =>
  rcases ewp_succ.1 h with ⟨v, rfl, hq⟩ | ⟨K, m, i, v, s, rfl, hK, hs, σa, σk, hd, rfl, hA, hB, hC⟩ |
    ⟨K, m, i, v, R, rfl, hK, hR, hRv⟩ | ⟨hnv, hst⟩
  · exact hq.elim
  · rw [← ccK_plug, ← Kont.plug_comp]
    refine ewp_perform _ (by rw [hasHnd_comp, ccK_hasHnd, hK]; rfl) (hperf _ _ _ hs) hd hA ?_ ?_
    · intro k hk w σw hw hb
      rw [Kont.plug_comp, ccK_plug]
      exact ih k (by omega) _ _ (hB k hk w σw hw hb)
    · intro C hc
      rw [dead_comp, ccK_dead]
      simpa [Kont.comp] using hC C hc
  · simp only [cancelProt] at hR
    split at hR
    · rename_i hmi
      obtain ⟨rfl, rfl⟩ := hmi
      cases hR
      obtain ⟨rfl, rfl⟩ := hRv
      have hstep := fun μ => step1Only_plug (ℍ := ℍ) (Head.cancel μ K hK) rfl .hole
      simp only [Kont.plug_hole] at hstep
      exact ewp_det hstep (ewp_val (hQ' n))
    · cases hR
  · rw [← ccK_plug, ← un_emp_right σ]
    refine ewp_ctx_step _ (disj_emp_right σ) hnv hst fun e' σ' _ he' => ?_
    rw [un_emp_right, ccK_plug]
    exact ih n (by omega) _ _ he'

/-! ### Finalisers -/

/-- The finaliser's postcondition: it answers `()` and has released everything it owned. -/
def QD : Post := fun _ v σ => v = Val.unit ∧ σ = emp

/-- A finaliser's protocol: must-resume operations only, and no raise. -/
structure FinProt (PD : Prot) : Prop where
  lin : ∀ m i s, PD.perf m i = some s → s.cancel = none
  rais : ∀ m i, PD.rais m i = none

/-- The finaliser's run in a frame `K` that catches nothing the finaliser does, framing `σ₂`. -/
theorem bindOK_fin {PD P' : Prot} (hPD : FinProt PD)
    (hle : ∀ m i s, PD.perf m i = some s → P'.perf m i = some s) {K : Kont} {σ₂ : Heap}
    (hK : ∀ m, K.HasHnd m = false) : BindOK K σ₂ PD P' where
  perf := fun m i s hs => ⟨hK m, s, hle m i s hs, rfl, rfl, fun C' hc' => by
    rw [hPD.lin m i s hs] at hc'; cases hc'⟩
  rais := fun m i R hR => by rw [hPD.rais m i] at hR; cases hR

/-- **The finaliser rule.** -/
theorem ewp_ubind {Pin Pout PD : Prot} {Qin Qout : Post} {N D : Val} {σD : Heap}
    (hPD : FinProt PD) (hle : ∀ m i s, PD.perf m i = some s → Pout.perf m i = some s)
    (hN : ∀ k w σ, Disj σ σD → Qin (k + 1) w σ →
      ewp (ℍ := ℍ) Pout Qout k (.app (.val N) (.val w)) (un σ σD))
    (hD : ∀ k, ewp (ℍ := ℍ) PD QD k (.app (.val D) (.val Val.unit)) σD)
    (hperf : ∀ m i s, Pin.perf m i = some s → ∃ s', Pout.perf m i = some s' ∧ s'.PA = s.PA ∧
      s'.PB = s.PB ∧ CancelExt s.cancel s'.cancel (ubK N D) σD)
    (hrais : ∀ m i R, Pin.rais m i = some R → ∃ R', Pout.rais m i = some R' ∧
      ∀ j k v σ, j ≤ k → R k v σ → R' j v σ ∧ (m = 0 → i = 0 ∧ ∃ err, v = errVal err)) :
    ∀ n M σ, Disj σ σD → ewp (ℍ := ℍ) Pin Qin n M σ →
      ewp (ℍ := ℍ) Pout Qout n (ubindE (.pair N D) M) (un σ σD) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M σ hdD h
  cases n with
  | zero => exact ewp_zero _ _
  | succ n =>
  rcases ewp_succ.1 h with ⟨v, rfl, hq⟩ | ⟨K, m, i, v, s, rfl, hK, hs, σa, σk, hd, rfl, hA, hB, hC⟩ |
    ⟨K, m, i, v, R, rfl, hK, hR, hRv⟩ | ⟨hnv, hst⟩
  · have hstep := fun μ => then_ret (ℍ := ℍ) μ N D v .hole
    simp only [Kont.plug_hole] at hstep
    exact ewp_det hstep (hN n v σ hdD hq)
  · obtain ⟨s', hs', hPA, hPB, hCE⟩ := hperf _ _ _ hs
    obtain ⟨hdaD, hdkD⟩ := disj_un_left.1 hdD
    rw [← ubK_plug, ← Kont.plug_comp, un_assoc]
    refine ewp_perform _ (by rw [hasHnd_comp, ubK_hasHnd, hK]; rfl) hs'
      (disj_un_right.2 ⟨hd, hdaD⟩) (hPA ▸ hA) ?_ ?_
    · intro k hk w σw hw hb
      obtain ⟨hdkw, hdDw⟩ := disj_un_left.1 hw
      have e₁ : un (un σk σD) σw = un (un σk σw) σD := by
        rw [un_assoc, un_comm hdDw, ← un_assoc]
      rw [Kont.plug_comp, ubK_plug, e₁]
      exact ih k (by omega) _ _ (disj_un_left.2 ⟨hdkD, hdDw.symm⟩) (hB k hk w σw hdkw (hPB ▸ hb))
    · intro C' hc'
      obtain ⟨C, hc, hCC⟩ := hCE C' hc'
      rw [dead_comp, Kont.plug_comp]
      have := hCC _ _ _ hdkD (hC C hc)
      rwa [ubK_dead] at this
  · obtain ⟨R', hR', hRR⟩ := hrais _ _ _ hR
    by_cases hm : m = 0
    · subst hm
      obtain ⟨hi, err, hv⟩ := (hRR n n v σ le_rfl hRv).2 rfl
      subst hi hv
      change ewp _ _ _ (ubindE _ (K.plug (raiseE (.val (cancelVal err))))) _
      have hstep := fun μ => step1Only_plug (ℍ := ℍ) (Head.ufinC μ N D err K hK) rfl .hole
      simp only [Kont.plug_hole] at hstep
      refine ewp_det hstep ?_
      rw [un_comm hdD, ← cfK_plug]
      refine ewp_bind _ (bindOK_fin hPD hle (fun m => cfK_hasHnd _ m)) n _ _ hdD.symm ?_ (hD n)
      rintro k hkn w σ' - ⟨rfl, rfl⟩
      rw [un_emp_left, cfK_plug]
      refine ewp_pred fun k₁ hk₁ => ?_
      have hstep := fun μ => step1Only_plug (ℍ := ℍ) (Head.cfret μ err Val.unit) rfl .hole
      simp only [Kont.plug_hole] at hstep
      refine ewp_det hstep ?_
      refine ewp_pred fun k₂ hk₂ => ?_
      exact ewp_raise (K := .hole) rfl hR' (hRR k₂ n _ σ (by omega) hRv).1
    · have hstep' := fun μ => (then_fin (ℍ := ℍ) (μ := μ) (i := i) N D v hm hK .hole).1
      simp only [Kont.plug_hole] at hstep'
      refine ewp_det hstep' ?_
      rw [un_comm hdD]
      refine ewp_bind _ (bindOK_fin hPD hle (fun _ => rfl)) n _ _ hdD.symm ?_ (hD n)
      rintro k hkn w σ' - ⟨rfl, rfl⟩
      rw [un_emp_left]
      refine ewp_pred fun k₁ hk₁ => ?_
      refine ewp_head (K := .hole) (fun μ => Head.seq μ _) rfl ?_
      refine ewp_pred fun k₂ hk₂ => ?_
      exact ewp_raise (K := .hole) rfl hR' (hRR k₂ n _ σ (by omega) hRv).1
  · rw [← ubK_plug]
    refine ewp_ctx_step _ hdD hnv hst fun e' σ' hd' he' => ?_
    rw [ubK_plug]
    exact ih n (by omega) _ _ hd' he'

/-- **A finaliser frame keeps the cancel obligation**, owning `σ_D` more: the cancelled region now
runs `D` when the cancel reaches the frame, and `D` releases `σ_D`. -/
theorem cancelObl_ubind {Pc : UInt32 → UInt32 → Option OpSpec} (hc : LinRow Pc) {PD : Prot}
    (hPD : FinProt PD) (hle : ∀ m i s, PD.perf m i = some s → Pc m i = some s) {N D : Val}
    {σD : Heap} (hD : ∀ k, ewp (ℍ := ℍ) PD QD k (.app (.val D) (.val Val.unit)) σD) :
    ∀ k x σ, Disj σ σD → cancelObl (ℍ := ℍ) Pc k x σ →
      cancelObl (ℍ := ℍ) Pc k (ubindE (.pair N D) x) (un σ σD) := by
  intro k x σ hd h
  refine ewp_ubind (Pin := cancelProt Pc) hPD hle (fun _ _ _ _ h => h.elim) hD ?_ ?_ k x σ hd h
  · intro m i s hs
    refine ⟨s, hs, rfl, rfl, fun C' hc' => ?_⟩
    rw [hc.lin m i s hs] at hc'; cases hc'
  · intro m i R hR
    refine ⟨R, hR, fun j k v σ _ hr => ⟨?_, ?_⟩⟩
    · simp only [cancelProt] at hR
      split at hR
      · cases hR; exact hr
      · cases hR
    · intro hm
      simp only [cancelProt] at hR
      split at hR
      · rename_i hmi; cases hR; exact ⟨hmi.2, none, hr.1⟩
      · cases hR

/-- **A context that catches nothing and holds no handler keeps the cancel obligation.** -/
theorem cancelObl_ctx {Pc : UInt32 → UInt32 → Option OpSpec} (hc : LinRow Pc) {K : Kont}
    (hH : ∀ m, K.HasHnd m = false) (hC : ∀ m, K.Catches m = false) :
    ∀ k x σ, cancelObl (ℍ := ℍ) Pc k x σ → cancelObl (ℍ := ℍ) Pc k (K.plug x) σ := by
  intro k x σ h
  rw [← un_emp_right σ]
  refine ewp_bind K ⟨fun m i s hs => ⟨hH m, s, hs, rfl, rfl, fun C' hc' => by
      rw [hc.lin m i s hs] at hc'; cases hc'⟩,
    fun m i R hR => ⟨hC m, R, hR, fun k v σ _ hr => by rwa [un_emp_right]⟩⟩ k x σ
    (disj_emp_right σ) (fun _ _ _ _ _ h => h.elim) h

end BoCa.Fig16.LogRel.Core.Chain.SI

end
