import Core.Chain.FuelKW835N
import Core.Chain.ImmLend833N
import Core.Chain.Unwind833N
import Core.Chain.FamImm836N
import Core.Chain.FamImmKW835N
import Core.Chain.FamOpsKW835N

/-!
# The lends at an unwinding row, at the typed world  `[spec §62]`

The lends at an unwinding row at `SemJN`: `withbor (1)` and `withbor (2)` (`withbor1U_compatN`,
`withbor2U_compatN`, over `ImmLend833N`'s steps), `withbor (3)` and `withload`
(`withbor3U_compatN`, `withloadU_compatN`, over `Unwind833N`'s anti-frame), `slice_borrow_mut`
(`sliceBorrowMU_compatN`, over `FamCancel836N`'s frame) and `slice_borrow`
(`sliceBorrowIU_compatN`, over `FamImm836N`'s frame).

An unwinding row's operations are abortive (`Row.Unwind`): a run at its table stops only at
`raise`s, which owe no continuation and read no world. So `F_Σ R` at such a row is one run at one
world (`cN_unwind_iff`), at the table `tabUN` at that world, whose payloads are read at `vN`
(`erwpK_abort_move`: a run at a table of abortive entries moves to any world whose location family
is the same and whose table has, at each key, an abortive entry with a weaker payload). The
chain's frames at `erwp` (`erwp_I_frameR`, `erwp_M_frameR`, `erwp_ubindRaise`) then apply, with
`tabUN`'s facts (`tabUN_abort`, `tabUN_named`, `tabUN_iLendOKR`, `tabUN_lendOKR`,
`tabUN_eq_addImm`, `tabUN_eq_add`) in place of `tabN`'s.

**The finaliser at its own row** (K-b): the lends' callback runs at `Σ_M` at one world as above,
and the result at `Σ ≥ Σ_M, Σ_D` at the worlds of `Σ`'s tables (`cN_effOf_tabF`). The finaliser
frame is `erwpK_unwindD`, which runs `D (); raise p` at the raise's world (`seq_raise_runK`), the
finaliser read from the claim at `Σ_D` (`fin_claimID`, `fin_claimMD`). Today's lends are the
instances at `Σ_D = ∅`, `Σ_M = Σ` (`withbor1U_sem`, …).  `[spec §19, §27]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload)

/-- **A run at a table of abortive entries moves to another world**: its stops are `raise`s, which
read no world and owe nothing; so it is a run at any world whose location family is the first's,
at a table with an abortive entry of a weaker payload at each key, its values posted there. -/
theorem erwpK_abort_move {ι ι' : Type} {V : ι → ι → Prop} {V' : ι' → ι' → Prop}
    {Φ : ι → LocFam} {Φ' : ι' → LocFam} {lo : ι → Life} {lo' : ι' → Life} {T : ι → OpTabK ι}
    {T' : ι' → OpTabK ι'} {Q : ι → PostN} {Q' : ι' → PostN} {x : ι} {x' : ι'}
    (hΦ : Φ' x' = Φ x) (hV : V' x' x') (hQ : ∀ y k ls v ρ, V x y → Q y k ls v ρ → Q' x' k ls v ρ)
    (hA : ∀ m i en, T x m i = some en → en.abort = true)
    (hR : ∀ m i en, T x m i = some en → ∃ en', T' x' m i = some en' ∧ en'.abort = true ∧
      ∀ k ls v ρ, en.PA k ls v ρ → en'.PA k ls v ρ)
    {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : erwpK (ℍ := ℍ) V Φ (fun z => opTableK (lo z) (T z)) Q x n ls e ρ) :
    erwpK (ℍ := ℍ) V' Φ' (fun z => opTableK (lo' z) (T' z)) Q' x' n ls e ρ := by
  rw [erwpK_eq] at h ⊢
  rw [hΦ]
  refine rwpG_mono (fun k ls t ρ ht => ?_) h
  rcases ht with ⟨v, hv, y, hy, hq⟩ | ⟨K, m, i, v, en, hp⟩ | ⟨K, m, i, v, en, hp⟩
  · exact Or.inl ⟨v, hv, x', hV, hQ y _ _ _ _ hy hq⟩
  · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
    rw [hA m i en hTe] at ha; cases ha
  · obtain ⟨⟨h₁, h₂, hTe, -⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    obtain ⟨en', hT', hab, hPA'⟩ := hR m i en hTe
    exact Or.inr (Or.inr ⟨K, m, i, v, en', pure_sep_mk ⟨h₁, h₂, hT', hab⟩
      ⟨ρa, ρn, hcan, ⟨hPA' _ _ _ _ hPA, hnA⟩, hnn⟩⟩)

section UnwindD
open BoCa.BoLo (ubindE)
variable {ι M : Type} {R : RowRd ι M}

/-- **The finaliser frame around a one-world run at an abortive table, its finaliser at its own
row** (`erwp_ubindRaise` with `[finalise]` at `erwpK`): the body `M` runs at one location family
`R.Φ x`, at a table `T` of abortive entries whose raises carry `Rc`. A return runs `N` at the world
`x`; a `raise` runs `D (); raise p` at `x` (`seq_raise_runK`), `D` from the claim at `Σ_D ≤ Σ`, the
raise's entry the one `Σ` holds at its key, its payload persistent where `Σ_D` may stop at an
unrestricted operation.  `[spec §19, §27]` -/
theorem erwpK_unwindD (hR : R.OK) (hPE : R.PayExt) (S SD : Row) (hDS : RowLe SD S) {μ : M}
    {T : OpTabN} (hTa : ∀ m i en, T m i = some en → en.abort = true)
    (hTr : ∀ m i en, T m i = some en → m ≠ 0) {x : ι} (hx : R.Inv x)
    (hTS : ∀ m i en, T m i = some en → ∃ o, Row.find S m i = some o ∧ o.abort = true ∧
      (SD.UnrD → o.A.Persistent) ∧
      ∀ k ls v ρ, en.PA k ls v ρ → R.vr o.A R.δ (R.Θ x) k v ρ)
    {Rc : Nat → WProp} (N D : Val) {Qd : ι → PostN}
    (hQd : ∀ y k ls v ρ, Qd y k ls v ρ → v = .unit ∧ NoOwn ρ)
    {Qin : PostN} {Qout : ι → PostN} (hQout : ∀ y, (Qout y).Down) (n : Nat)
    (hD : ∀ k, k ≤ n → ∀ ls ρ, Rc k ρ → erwpK (ℍ := ℍ) R.V R.Φ
      (fun z => opTableK (R.fl z) (tabF (ℍ := ℍ) R μ (CTy.effOf SD .unit) z)) Qd x k ls
      (.app (.val D) (.val .unit)) ρ)
    (hN : ∀ k, k ≤ n → ∀ ls (v : Val) ρ, Qin k ls v ρ → erwpK (ℍ := ℍ) R.V R.Φ
      (fun z => opTableK (R.fl z) (tabF (ℍ := ℍ) R μ (CTy.effOf S .unit) z)) Qout x k ls
      (.app (.val N) (.val v)) ρ) :
    ∀ ls M ρ, erwp (ℍ := ℍ) (R.Φ x) (opTableR T Rc) Qin n ls M ρ →
      erwpK (ℍ := ℍ) R.V R.Φ
        (fun z => opTableK (R.fl z) (tabF (ℍ := ℍ) R μ (CTy.effOf S .unit) z)) Qout x n ls
        (ubindE (.pair N D) M) ρ := by
  intro ls M ρ h
  have hΦ := hR.ΦDown x hx
  have hLo : ∀ z, (opTableK (R.fl z) (tabF (ℍ := ℍ) R μ (CTy.effOf S .unit) z)).Local :=
    fun z => opTableK_local _ _
  have hPD := erwpPostK_down (V := R.V x)
    (opTableK_downI (lo := R.fl x) (tabF_downI hR μ (CTy.effOf S .unit) x)) (Q := Qout) hQout
  rw [← ubK_plug, erwpK_eq]
  refine rwpG_bind hΦ (ubK N D) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwp_unfold_at (opTableR_local T Rc) le_rfl h)
  rcases ht with ⟨v, rfl, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · -- `[then]`: `N` at the world `x`
    have hstep := fun μ' => then_ret (ℍ := ℍ) μ' N D v .hole
    simp only [Kont.plug_hole] at hstep
    exact rwpG_det hΦ (hPD _) hstep (erwpK_unfold_at hLo hk (hN k hk ls' v σ hv))
  · -- the table is abortive: no `perform`
    obtain ⟨⟨-, -, hT, ha⟩, -⟩ := pure_sep_iff.mp hp
    rw [hTa m i en hT] at ha; cases ha
  · -- `[finalise]`: `D (); raise p` at `x`, `D` from the claim
    obtain ⟨⟨rfl, hK₁, hT, -⟩, σ₁, ρR, hcσ, ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩, hRc⟩ :=
      pure_sep_iff.mp hp
    obtain ⟨o, hfo, hao, hpers, hvr⟩ := hTS m i en hT
    have hm0 := hTr m i en hT
    refine rwpG_det hΦ (hPD _)
      (fun μ' => (then_fin (ℍ := ℍ) (μ := μ') (i := i) N D v hm0 hK₁ .hole).1) ?_
    rw [Kont.plug_hole]
    -- the payload beside the finaliser, the leftover `NoOwn` part as garbage
    obtain ⟨X, hX, hcX⟩ := compS_exch hcan hcσ
    have hrun := seq_raise_runK (ℍ := ℍ) hR hPE S SD hDS hfo hao (μ := μ) hQd hQout k x hx ls'
      _ ρR (hD k hk ls' ρR hRc) ρa X ⟨hvr k ls' v ρa hPA, hnA⟩
      (fun hu => hR.vrPers _ (hpers hu) _ _ _ _ (hvr k ls' v ρa hPA)) (ResU.CompS.comm hX)
    exact erwpK_unfold_at hLo hk (erwpK_garbage hcX hnn hrun)

end UnwindD

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head ubindE)

/-! ### An unwinding row's table at a world -/

/-- **An unwinding row's table at a world, its payloads at `vN`**: at each operation of the row,
an entry whose payload is `𝒱⟦A⟧` at the world and whose answer is empty. -/
def tabUN (S : Row) (δ : LSub) (Θ : LocTy) : OpTabN :=
  fun m i => (Row.find S m i).map (fun o =>
    entN o.q o.B (fun k v ρ => vN (ℍ := ℍ) o.A δ Θ k v ρ) (fun _ _ _ => False) none)

theorem tabUN_some {S : Row} {δ : LSub} {Θ : LocTy} {m i : UInt32} {en : OpEntN}
    (h : tabUN (ℍ := ℍ) S δ Θ m i = some en) :
    ∃ o ∈ S, m = o.n ∧ en = entN o.q o.B (fun k v ρ => vN (ℍ := ℍ) o.A δ Θ k v ρ)
      (fun _ _ _ => False) none := by
  obtain ⟨o, hf, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨ho, hn, -⟩ := Row.find_mem hf
  exact ⟨o, ho, hn.symm, rfl⟩

/-- **An unwinding row's payload values lie in every stratum**. -/
theorem vN_unwind_inStratumK {S : Row} {x : LifeVar} (hS : S.Unwind x) {o : OpSig} (ho : o ∈ S)
    (δ : LSub) (α : Life) : ∀ (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes),
      vN (ℍ := ℍ) o.A δ Θ n v ρ → ρ.InStratum α := by
  intro Θ n v ρ h
  rw [← vN_extend_of_not_free (hS o ho).2.2.1 δ α] at h
  exact vN_outlives (models_empty_any _) (interp_ext_self δ x α)
    ((hS o ho).2.2.2 LifeCtx.empty (.var x)) Θ n v ρ h

/-- **Every entry of an unwinding row's table is abortive.** -/
theorem tabUN_abort {S : Row} {x : LifeVar} (hS : S.Unwind x) (δ : LSub) (Θ : LocTy) :
    ∀ m i en, tabUN (ℍ := ℍ) S δ Θ m i = some en → en.abort = true := by
  intro m i en h
  obtain ⟨o, ho, -, rfl⟩ := tabUN_some h
  exact (hS o ho).1

/-- An unwinding row's raises are at named operations. -/
theorem tabUN_named {S : Row} {x : LifeVar} (hS : S.Unwind x) (δ : LSub) (Θ : LocTy) :
    ∀ m i en, tabUN (ℍ := ℍ) S δ Θ m i = some en → en.abort = true → m ≠ 0 := by
  intro m i en h _
  obtain ⟨o, ho, rfl, rfl⟩ := tabUN_some h
  exact (hS o ho).2.1

theorem tabUN_down (S : Row) (δ : LSub) (Θ : LocTy) : (tabUN (ℍ := ℍ) S δ Θ).Down where
  pa := fun m i en h k ls v ρ hp => by
    obtain ⟨o, -, -, rfl⟩ := tabUN_some h
    exact vN_down _ δ Θ k v ρ hp
  fin := fun m i en P h hP => by
    obtain ⟨o, -, -, rfl⟩ := tabUN_some h
    simp [entN] at hP
  wcl := fun m i en h ls ls' ρ₁ ρ₂ ρ hc he => by
    obtain ⟨o, -, -, rfl⟩ := tabUN_some h
    exact extF_left ls ls' ρ₁ ρ₂ ρ hc he

/-- **An unwinding row's table may be stopped at under an `imm` lend at any `α`** -/
theorem tabUN_iLendOKR {S : Row} {x : LifeVar} (hS : S.Unwind x) (δ : LSub) (Θ : LocTy)
    (α : Life) : (tabUN (ℍ := ℍ) S δ Θ).ILendOKR α where
  entry := fun m i en h ha => by
    rw [tabUN_abort hS δ Θ m i en h] at ha; cases ha
  pa := fun m i en h k ls v ρ hp => by
    obtain ⟨o, ho, -, rfl⟩ := tabUN_some h
    exact vN_unwind_inStratumK hS ho δ α Θ k v ρ hp
  pb := fun m i en h k ls w ρ hp => by
    obtain ⟨o, ho, -, rfl⟩ := tabUN_some h
    exact hp.elim
  paExt := fun m i en h k ls₁ ls₂ v ρ _ hp => by
    obtain ⟨o, ho, -, rfl⟩ := tabUN_some h
    exact hp
  pbExt := fun m i en h k ls₁ ls₂ w ρ _ hp => by
    obtain ⟨o, ho, -, rfl⟩ := tabUN_some h
    exact hp

/-- **An unwinding row's table may be stopped at under a `mut` lend at any `α`** -/
theorem tabUN_lendOKR {S : Row} {x : LifeVar} (hS : S.Unwind x) (δ : LSub) (Θ : LocTy)
    (α : Life) : (tabUN (ℍ := ℍ) S δ Θ).LendOKR α where
  entry := fun m i en h ha => by
    rw [tabUN_abort hS δ Θ m i en h] at ha; cases ha
  pa := fun m i en h k ls v ρ hp => by
    obtain ⟨o, ho, -, rfl⟩ := tabUN_some h
    exact vN_unwind_inStratumK hS ho δ α Θ k v ρ hp
  pb := fun m i en h k ls w ρ hp => by
    obtain ⟨o, ho, -, rfl⟩ := tabUN_some h
    exact hp.elim

/-- An unwinding row's table at a world agrees with another at every payload its row reads
alike. -/
theorem tabUN_congr {S : Row} {δ δ' : LSub} {Θ Θ' : LocTy}
    (h : ∀ o ∈ S, vN (ℍ := ℍ) o.A δ' Θ' = vN (ℍ := ℍ) o.A δ Θ) :
    tabUN (ℍ := ℍ) S δ' Θ' = tabUN (ℍ := ℍ) S δ Θ := by
  funext m i
  simp only [tabUN]
  cases hf : Row.find S m i with
  | none => rfl
  | some o =>
      simp only [Option.map_some]
      rw [h o (Row.find_mem hf).1]

/-- **An unwinding row's table does not read `'x`, the record of a lend at `α`, nor its base** -/
theorem tabUN_eq_addImm {S : Row} {x : LifeVar} (hS : S.Unwind x) (δ : LSub) (Θ : LocTy)
    (r : FrameRec) (α : Life) :
    tabUN (ℍ := ℍ) S (δ.extend x α) (Θ.addImm (r, α)) = tabUN (ℍ := ℍ) S δ Θ := by
  refine tabUN_congr fun o ho => ?_
  rw [vN_extend_of_not_free (hS o ho).2.2.1 δ α]
  funext n v ρ
  have hρ := vN_unwind_inStratumK hS ho δ α
  exact propext ⟨fun h => vN_extR _ δ n v ρ (LocTy.extR_of_addImm Θ r (hρ _ n v ρ h)) h,
    fun h => vN_extR _ δ n v ρ (LocTy.extR_addImm Θ r (hρ _ n v ρ h)) h⟩

/-- **An unwinding row's table does not read `'x`, nor a `mut` lend at a fresh `α`** -/
theorem tabUN_eq_add {S : Row} {x : LifeVar} (hS : S.Unwind x) (δ : LSub) {Θ : LocTy}
    {α : Life} (hfr : Θ.Fresh α) (l : Loc) (F : Nat → Val → SPropS Loc Val α) :
    tabUN (ℍ := ℍ) S (δ.extend x α) (Θ.add l α F) = tabUN (ℍ := ℍ) S δ Θ := by
  refine tabUN_congr fun o ho => ?_
  rw [vN_extend_of_not_free (hS o ho).2.2.1 δ α]
  funext n v ρ
  have hρ := vN_unwind_inStratumK hS ho δ α
  exact propext ⟨fun h => vN_local _ δ Θ l α F n v ρ (hρ _ n v ρ h) h,
    fun h => vN_extA _ δ (LocTy.extA_add hfr l F) n v ρ h⟩

/-- **`F_Σ R` at an unwinding row is one run at one world**: at every floor, a run at `cN`'s
table stops only at `raise`s, so it is the run at `erwp` at `tabUN` (`erwpK_abort_move`, both
ways). -/
theorem cN_unwind_iff {S : Row} {x : LifeVar} (hS : S.Unwind x) {R : VTy} {δ : LSub}
    {Θ : LocTy} {c : Loc → Option Life} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes} :
    cN (ℍ := ℍ) (CTy.effOf S R) δ Θ c n ls e ρ ↔
      erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabUN (ℍ := ℍ) S δ Θ))
        (fun k _ v ρ => vN (ℍ := ℍ) R δ Θ k v ρ) n ls e ρ := by
  have hfind : ∀ (y : KW) m i,
      tabN (ℍ := ℍ) (CTy.effOf S R) δ y m i = (Row.find S m i).map (fun o =>
        (rdN (ℍ := ℍ) δ).ent () m o.q o.A o.B (finF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () o.fin) y) := by
    intro y m i
    rw [tabN_eq, tabF_effOf_find]
  rw [cN_effOf, erwp_opTableN_eq_erwpK 0]
  constructor
  · intro h
    refine erwpK_abort_move (x := (⟨Θ, c, 0⟩ : KW)) (x' := ()) rfl trivial
      (fun y k ls v ρ (hy : y = _) hq => by subst hy; exact hq) ?_ ?_ (h 0)
    · intro m i en hT
      rw [hfind] at hT
      obtain ⟨o, hf, rfl⟩ := Option.map_eq_some_iff.mp hT
      exact (hS o (Row.find_mem hf).1).1
    · intro m i en hT
      rw [hfind] at hT
      obtain ⟨o, hf, rfl⟩ := Option.map_eq_some_iff.mp hT
      refine ⟨liftEntK (entN o.q o.B (fun k v ρ => vN (ℍ := ℍ) o.A δ Θ k v ρ)
        (fun _ _ _ => False) none), liftTabK_of_some (show tabUN (ℍ := ℍ) S δ Θ m i = some _ by
        simp only [tabUN, hf, Option.map_some]), (hS o (Row.find_mem hf).1).1,
        fun _ _ _ _ h => h⟩
  · intro h lo
    refine erwpK_abort_move (x := ()) (x' := (⟨Θ, c, lo⟩ : KW)) rfl (KW.postK_refl _)
      (fun _ _ _ _ _ _ hq => hq) ?_ ?_ h
    · intro m i en hT
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
      exact tabUN_abort hS δ Θ m i en₀ h₀
    · intro m i en hT
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
      obtain ⟨o, hf, rfl⟩ := Option.map_eq_some_iff.mp h₀
      exact ⟨(rdN (ℍ := ℍ) δ).ent () m o.q o.A o.B (finF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () o.fin)
        ⟨Θ, c, lo⟩, by rw [hfind]; simp only [hf, Option.map_some], (hS o (Row.find_mem hf).1).1,
        fun _ _ _ _ h => h⟩

/-! ### The finaliser at the lend's claim -/

/-- **The finaliser `λ_. d ℓ` consumes an `imm` lend's claim**: the cell owned again with the
content it was lent with, `d`'s judgment at `Ref A ⊸ 1` read at the world and an index below the
content's. -/
theorem fin_claimI {A : VTy} {d : Expr} {δ : LSub} {Θ : LocTy}
    (hΘ : Θ.OK) {c : Loc → Option Life} {N : Nat}
    (hd : ∀ k, k ≤ N → ∀ ls, cN (ℍ := ℍ) (.ret (.lolli (.ref A) .unit)) δ Θ c k ls d PMap.empty)
    {l : Loc} {w : Val} {σ : WRes} (hw : vN (ℍ := ℍ) A δ Θ N w σ) {k : Nat} (hk : k ≤ N)
    {ls : List SRec} {ρ : WRes} (h : claimI l w σ k ρ) (hc : ConsistentX c ρ) :
    rwp (ℍ := ℍ) (Θ.view c) (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
      (.app (.val (DFv (d.shift 1 0) l)) (.val .unit)) ρ := by
  have hΦ := LocTy.view_down hΘ.1 c
  refine Hardest791.rwp_det'' (Q := fun _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) hΦ
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (.app (d.shift 1 0) (.val (Val.loc l)))) =
      (Kont.appL .hole (Val.loc l)).plug d := by
    simp [Kont.plug, Expr.subst, subst_shift_succ (j := 0) (d := 0) _ d (le_refl _), Expr.shift_zero, Val.loc]
  rw [e]
  refine rwp_bind hΦ _ ?_
  have hd0 := hd k hk ls
  have hfr := rwp_frame (fun _ τ => τ = ρ) (fun _ _ _ _ h => h) (compS_empty_left ρ)
    (rwp_of_erwp_empty (erwp_of_cN_ret hd0)) rfl
  refine rwp_mono_le (fun k' hk' ls' v τ hv => ?_) (rwp_consistentXV hfr hc)
  obtain ⟨⟨τ₁, τ₂, hcτ, hP, rfl⟩, hcτ', hvτ⟩ := hv
  have := hP Θ (LocTy.extR_refl Θ _) hΘ c (consistentX_left hcτ hcτ' hvτ) ls'
    c k' le_rfl (Val.loc l) τ₂ τ hcτ
    ⟨l, w, σ, rfl, h, vN_le (hk'.trans hk) hw⟩ hcτ'
  exact rwp_of_erwp_empty (erwp_of_cN_ret this)

/-! ### The finaliser at its own row -/

/-- **The finaliser `λ_. d ℓ` at its own row, from the source handed back**: `d`'s judgment at
`U(src ⊸ F_{Σ_D} 1)` read at the world and an index at or below `N`, the source a value of `src`
at `ℓ`; the run is at `Σ_D`'s tables from the world `⟨Θ, c, lo⟩` (`erwpK_bindR`: `d` to its value,
then the value applied there, `cN_effOf_tabF`).  `[spec §19, §27]` -/
theorem fin_claimD {src : VTy} {SD : Row} {d : Expr} {δ : LSub} {Θ : LocTy} (hΘ : Θ.OK)
    {c : Loc → Option Life} (lo : Life) {N : Nat}
    (hd : ∀ k, k ≤ N → ∀ ls, cN (ℍ := ℍ) (.ret (.thunk (.arr src (CTy.effOf SD .unit)))) δ Θ c
      k ls d PMap.empty)
    {l : Loc} {k : Nat} (hk : k ≤ N) {ls : List SRec} {ρ : WRes}
    (h : vN (ℍ := ℍ) src δ Θ k (Val.loc l) ρ) (hc : ConsistentX c ρ) :
    erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
      (fun z => opTableK z.lo (tabF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () (CTy.effOf SD .unit) z))
      (fun z k _ v ρ => vN (ℍ := ℍ) .unit δ z.Θ k v ρ) ⟨Θ, c, lo⟩ k ls
      (.app (.val (DFv (d.shift 1 0) l)) (.val .unit)) ρ := by
  have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
  have hL : ∀ z : KW, (opTableK z.lo (tabF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () (CTy.effOf SD .unit)
      z)).Local := fun z => opTableK_local _ _
  refine erwpK_det (x := (⟨Θ, c, lo⟩ : KW)) hΦ
    (opTableK_downI (tabF_downI (rdN_ok δ) () (CTy.effOf SD .unit) _))
    (fun z k _ v ρ h => vN_down _ δ z.Θ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (.app (d.shift 1 0) (.val (Val.loc l)))) =
      (Kont.appL .hole (Val.loc l)).plug d := by
    simp [Kont.plug, Expr.subst, subst_shift_succ (j := 0) (d := 0) _ d (le_refl _),
      Expr.shift_zero, Val.loc]
  rw [e]
  refine erwpK_bindR hL hΦ (Kont.appL .hole (Val.loc l)) ?_
  have hfr := rwp_frame (fun _ τ => τ = ρ) (fun _ _ _ _ h => h) (compS_empty_left ρ)
    (rwp_of_erwp_empty (erwp_of_cN_ret (hd k hk ls))) rfl
  refine rwp_mono_le (fun k' hk' ls' v τ hv => ?_) (rwp_consistentXV hfr hc)
  obtain ⟨⟨τ₁, τ₂, hcτ, hP, rfl⟩, hcτ', hvτ⟩ := hv
  have hC := hP Θ (LocTy.extR_refl Θ _) hΘ c (consistentX_left hcτ hcτ' hvτ) ls'
    c k' le_rfl (Val.loc l) τ₂ τ hcτ (vN_le hk' h) hcτ'
  exact (cN_effOf_tabF SD .unit δ Θ c k' ls' _ τ).mp hC lo

/-- **`fin_claimD` at an `imm` lend's claim**: the cell owned again with the content it was lent
with, a `Ref A` value (`fin_claimI` at `Σ_D`).  `[spec §19, §27]` -/
theorem fin_claimID {A : VTy} {SD : Row} {d : Expr} {δ : LSub} {Θ : LocTy} (hΘ : Θ.OK)
    {c : Loc → Option Life} (lo : Life) {N : Nat}
    (hd : ∀ k, k ≤ N → ∀ ls, cN (ℍ := ℍ) (.ret (.thunk (.arr (.ref A) (CTy.effOf SD .unit))))
      δ Θ c k ls d PMap.empty)
    {l : Loc} {w : Val} {σ : WRes} (hw : vN (ℍ := ℍ) A δ Θ N w σ) {k : Nat} (hk : k ≤ N)
    {ls : List SRec} {ρ : WRes} (h : claimI l w σ k ρ) (hc : ConsistentX c ρ) :
    erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
      (fun z => opTableK z.lo (tabF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () (CTy.effOf SD .unit) z))
      (fun z k _ v ρ => vN (ℍ := ℍ) .unit δ z.Θ k v ρ) ⟨Θ, c, lo⟩ k ls
      (.app (.val (DFv (d.shift 1 0) l)) (.val .unit)) ρ :=
  fin_claimD hΘ lo hd hk ⟨l, w, σ, rfl, h, vN_le hk hw⟩ hc

/-- **`fin_claimD` at a reborrow's source**: a `Mut @a A` value at `ℓ` (`fin_claimMN` at `Σ_D`).
`[spec §19, §27]` -/
theorem fin_claimMD {a : Lifetime.Life} {A : VTy} {SD : Row} {d : Expr} {δ : LSub} {Θ : LocTy}
    (hΘ : Θ.OK) {c : Loc → Option Life} (lo : Life) {N : Nat}
    (hd : ∀ k, k ≤ N → ∀ ls, cN (ℍ := ℍ) (.ret (.thunk (.arr (.mut a A) (CTy.effOf SD .unit))))
      δ Θ c k ls d PMap.empty)
    {l : Loc} {k : Nat} (hk : k ≤ N) {ls : List SRec} {ρ : WRes}
    (h : vN (ℍ := ℍ) (.mut a A) δ Θ k (Val.loc l) ρ) (hc : ConsistentX c ρ) :
    erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
      (fun z => opTableK z.lo (tabF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () (CTy.effOf SD .unit) z))
      (fun z k _ v ρ => vN (ℍ := ℍ) .unit δ z.Θ k v ρ) ⟨Θ, c, lo⟩ k ls
      (.app (.val (DFv (d.shift 1 0) l)) (.val .unit)) ρ :=
  fin_claimD hΘ lo hd hk h hc

/-! ### `withbor (1)` at an unwinding row -/

/-- **`withbor (1)` at an unwinding row is a value of its type**: `withborU d` at
`Ref A ⊸ (∀'x ⊏ @Δ. Imm 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ(Ref A ⊗ B)`, `Σ` a `Row.Unwind x` row. Core's
`withbor1U_compatX`, step by step:

1. the source `ℓ ↦ own(w₀) ● σ₀`, the callback `f`, read at the run's world `Θ` (`vN_extR`);
2. `withborU d ℓ f` steps to the callback under the finaliser frame `then b. (ℓ, b) unwind d ℓ`;
3. the lend at a lifetime `α` below the bound, the content's stratum and the callback's
   (Core's `a₂ ⊓ m` at the Imm Frame's `⋔`), the record `p = (ℓ, w₀, σ₀, A, δ)`;
4. the callback's world `Θ + (p, α)`, an extension at the callback's resource
   (`LocTy.extR_addImm`, Core's `ext_add hadd hout₂`);
5. the borrow `ℓ ↦ imm({α}, w₀, σ₀)` a value of `Imm 'x A` at `δ['x ↦ α]` there: its payload
   observable at `A`, its witness the record;
6. the callback's run, at the world's view, is one at `Θ`'s (`erwp_tieEntry`), its table the
   lender's (`tabUN_eq_addImm`);
7. the Imm Frame across the row's raises (`erwp_I_frameR`, Core's `ewpTS_I_frameU`), the
   callback's result `['x] B` back at `Θ` (`LocTy.extR_of_addImm`, Core's `ext_drop`);
8. the finaliser frame: at a return `(ℓ, b)`, at a raise `d ℓ` consumes the claim
   (`erwp_ubindRaise`, `fin_claimI`).

Premises: `hδ`, `hadm` (Core's `admWf_of_vScoped hsc₁ hδ`), `hfree₁`, `hfree₂`, `hS` are
the rule's; `hd` is the finaliser's judgment at the run's world and every lower index. -/
theorem withbor1UD_sem {Δ : LifeCtx} {x : LifeVar} {A B : VTy} {SM SD S : Row} {d : Expr} {δ : LSub}
    (hδ : Δ.Models δ) (hadm : AdmWf A δ) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B)
    (hS : SM.Unwind x) (hMS : RowLe SM S) (hDS : RowLe SD S)
    (hPend : SD.UnrD → SM.PendPers) (Θ₀ : LocTy) (n : Nat)
    (hd : ∀ (Θ : LocTy), Θ.OK → ∀ c k, k ≤ n → ∀ ls,
      cN (ℍ := ℍ) (.ret (.thunk (.arr (.ref A) (CTy.effOf SD .unit)))) δ Θ c k ls d PMap.empty) :
    vN (ℍ := ℍ) (withbor1UTyD x Δ.meetOfDom A B SM S) δ Θ₀ n (withborUV d) PMap.empty := by
  intro Θ _ hΘ c₁ _ ls c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  intro c k' hk' f ρf ρ'' hc' hf hcon
  -- step 1
  obtain ⟨l, w₀, σ₀, rfl, hcl, hw₀⟩ := vN_le hk' hu
  refine (cN_effOf_tabF S _ δ Θ c k' ls _ ρ'').mpr fun lo => ?_
  rw [tabF_effOf_ret (rdN (ℍ := ℍ) δ) () S (.tensor (.ref A) B) .unit]
  refine erwpK_of_valid fun hv'' => ?_
  have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
  set T := tabUN (ℍ := ℍ) SM δ Θ with hTdef
  have hTd : T.Down := tabUN_down SM δ Θ
  have hQo : ∀ y : KW, PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) (.tensor (.ref A) B) δ y.Θ k v ρ) :=
    fun y k _ v ρ h => vN_down _ δ y.Θ k v ρ h
  have hTo := opTableK_downI (lo := lo) (tabF_downI (rdN_ok (ℍ := ℍ) δ) () (CTy.effOf S .unit)
    (⟨Θ, c, lo⟩ : KW))
  -- step 2
  refine erwpK_det (x := (⟨Θ, c, lo⟩ : KW)) hΦ hTo hQo
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl (.appL .hole f)) ?_
  refine erwpK_det (x := (⟨Θ, c, lo⟩ : KW)) hΦ hTo hQo
    (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 f (Expr.subst (0 + 1) (Val.shift 1 0 (Val.loc l))
        (thenE ((Expr.var 2).pair (Expr.var 0)) ((d.shift 3 0).app (Expr.var 2))
          (((Expr.var 0).app (Expr.val Val.unit)).app (Expr.var 1))))) =
      ubindE (.pair (NFv l) (DFv (d.shift 1 0) l)) (.app (.app (.val f) (.val .unit)) (.val (Val.loc l))) := by
    simp [Kont.plug, Expr.subst, Expr.shift, thenE, ubindE, NFv, DFv, Val.shift, Val.pair,
      Val.loc, Val.lam, Expr.val, Val.prim, subst_shift_succ (j := 2) (d := 2) _ d (le_refl _),
      subst_shift_succ (j := 1) (d := 1) _ d (le_refl _)]
  rw [e₃]
  -- the parts of the start are consistent with the view
  have hvu : ResU.Valid ρu := (ResU.Valid.split hc' hv'').1
  have hcf : ConsistentX c ρf := consistentX_right hc' hcon hv''
  have hcσ : ConsistentX c σ₀ := consistentX_right hcl (consistentX_left hc' hcon hv'') hvu
  -- step 3: the lend's lifetime and record
  obtain ⟨γ, hγ⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  obtain ⟨βP, hβP⟩ := ResU.exists_stratum σ₀
  set α : Life := ↓(βP ⊓ βf ⊓ γ) with hαdef
  have hαlt : α < βP ⊓ βf ⊓ γ := Life.down_sqsubset _
  have houtP : σ₀.InStratum α := hβP.mono (hαlt.le.trans (inf_le_left.trans inf_le_left))
  have houtb : ρf.InStratum α := hβf.mono (hαlt.le.trans (inf_le_left.trans inf_le_right))
  have hLt : LtLife δ Δ.meetOfDom α := ⟨γ, hγ, lt_of_lt_of_le hαlt inf_le_right⟩
  set δ' := δ.extend x α with hδ'
  set p : FrameRec := ⟨l, w₀, σ₀, A, δ⟩ with hpdef
  -- the record's lineage
  have hvσ : ResU.Valid σ₀ := (ResU.Valid.split hcl hvu).2
  obtain ⟨-, eR, -, heR, -, -⟩ := hvσ
  obtain ⟨ds, hds⟩ := lineage_list (r := p) (vN_vShape A δ Θ k' w₀ σ₀ hw₀) hadm heR
  -- step 4: the callback's world
  set Θ' := Θ.addImm (p, α) with hΘ'
  have hOK' : Θ'.OK := ⟨fun l' b F h => hΘ.1 l' b F h,
    let ⟨N, hN⟩ := hΘ.2; ⟨N, fun l' b h => hN l' b h⟩⟩
  set ρi : WRes := ResU.single l (CellU.immOf (LSet.singleton α) w₀ σ₀ houtP) with hρi
  set P : List SRec → Val → WProp := fun _ v ρ => vN (ℍ := ℍ) A δ Θ k' v ρ with hP
  set Qb : PostN := fun k _ b ρ => vN (ℍ := ℍ) (.tensor (.ref A) B) δ Θ k
    (Val.pair (Val.loc l) b) ρ with hQb
  -- steps 5–7: the Imm Frame
  have hI := erwp_I_frameR (Φ := Θ.view c) l A δ hadm w₀ P
    (fun _ ρ h => vN_vShape A δ Θ k' w₀ ρ h) (fun _ _ _ _ h => h)
    (tabUN_iLendOKR hS δ Θ α) (Q := Qb) (fun _ _ _ _ _ _ h => h)
    k' ls (.app (.app (.val f) (.val .unit)) (.val (Val.loc l))) σ₀ ρu ρf ρ'' houtP houtb hw₀
    hcl hc' ds hds (fun BI hBI => ?_)
  · -- step 8: the finaliser frame
    have hI' := erwp_mono_le (Tb' := opTableR T (fun j ρ => claimI l w₀ σ₀ j ρ ∧ j ≤ k')) k'
      (fun _ _ _ _ _ h => h) (fun j hj ls' t Ψ Ψ' ρ hΨ h => by
        rcases h with ⟨K, m, i, v, en, h⟩ | ⟨K, m, i, v, en, h⟩
        · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp h
          exact absurd ha (by rw [tabUN_abort hS δ Θ m i en hTe]; decide)
        · obtain ⟨hp, τ, τR, hcτ, h₁, hR⟩ := pure_sep_iff.mp h
          exact Or.inr ⟨K, m, i, v, en, pure_sep_mk hp ⟨τ, τR, hcτ, h₁, hR, hj⟩⟩)
      k' le_rfl ls _ ρ'' hI
    refine erwpK_unwindD (R := rdN (ℍ := ℍ) δ) (rdN_ok δ) (rdN_payExt δ) S SD hDS (μ := ())
      (T := T) (tabUN_abort hS δ Θ)
      (fun m i en h => tabUN_named hS δ Θ m i en h (tabUN_abort hS δ Θ m i en h))
      (x := (⟨Θ, c, lo⟩ : KW)) hΘ.1 ?_ (NFv l) (DFv (d.shift 1 0) l)
      (Qd := fun z k _ v ρ => vN (ℍ := ℍ) .unit δ z.Θ k v ρ) ?_ hQo k' ?_ ?_ ls _ ρ'' hI'
    · -- the raise's entry, read in `Σ`
      intro m i en h
      obtain ⟨o, hf, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨o', hf', hle⟩ := hMS m i o hf
      have hab' : o.abort = true := (hS o (Row.find_mem hf).1).1
      refine ⟨o', hf', by rw [← hle.1.abort_eq]; exact hab', fun hu => ?_, fun k ls v ρ hp => ?_⟩
      · have h₁ := ((hPend hu) o (Row.find_mem hf).1).1 hab'
        rwa [hle.1.2.2.2.1] at h₁
      · show vN (ℍ := ℍ) o'.A δ Θ k v ρ
        rw [← hle.1.2.2.2.1]; exact hp
    · rintro y k ls' v σ ⟨rfl, rfl⟩
      exact ⟨rfl, noOwn_empty⟩
    · -- the finaliser at `Σ_D`, from the claim
      intro j hj ls' ρ hR
      obtain ⟨hcl', hj⟩ := hR
      have hcρ : ConsistentX c ρ :=
        consistentX_compS hcl' (consistentX_of_top (ResU.inStratum_single_own _ l w₀) c) hcσ
      exact fin_claimID hΘ lo (fun j hj ls => hd Θ hΘ c j (hj.trans (hk'.trans hk)) ls) hw₀ hj
        hcl' hcρ
    · -- a return: `(ℓ, b)` at the world `⟨Θ, c, lo⟩`
      intro j _ ls' b ρ hq
      refine erwpK_det (x := (⟨Θ, c, lo⟩ : KW)) hΦ hTo hQo
        (fun μ => step1Only_plug (Head.beta μ _ b) rfl .hole) ?_
      simp [Kont.plug, Expr.subst]
      exact erwpK_val (v := Val.pair (Val.loc l) b) (KW.postK_refl _) hq
  · -- step 5: the borrow at the callback's world
    have hvO : vO (ℍ := ℍ) A δ' Θ' k' w₀ σ₀ := by
      rw [vO_extend_of_not_free hfree₁]
      exact vO_extR A δ k' w₀ σ₀ (LocTy.extR_addImm Θ p houtP) (vN_vO A δ Θ k' w₀ σ₀ hw₀)
    have hcell : vN (ℍ := ℍ) (.imm (.var x) A) δ' Θ' k' (Val.loc l) ρi := by
      refine ⟨α, interp_ext_self δ x α, ⟨l, LSet.singleton α, w₀, σ₀, houtP, rfl, rfl,
        le_refl _, hvO⟩, fun l₀ s₀ u₀ σ₁ h₀ e => ?_⟩
      obtain ⟨rfl, e'⟩ := single_immOf_inj e
      obtain ⟨rfl, -⟩ := CellU.immOf_inj e'
      exact ⟨(p, α), List.mem_cons_self .., le_refl _, p, DescR.refl _, A, δ', TyEq.refl _ _,
        Or.inl ⟨p, List.mem_singleton_self _, rfl, rfl, fun y hy =>
          BoCa.Fig16.LogRel.find?_extend_ne δ α (fun e => by subst e; exact hfree₁ hy)⟩⟩
    have hcBI : ConsistentX c BI := consistentX_compS hBI hcf
      (consistentX_allImm (fun m ψ e => by
        obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
        exact CellU.kind_immOf _ _ _ _) c)
    -- step 6: the callback's run
    have h1 := (hf Θ' (LocTy.extR_addImm Θ p houtb) hOK' c hcf
      (frameList p ds α ls)) α hLt
    have h2 := h1 c k' le_rfl (Val.loc l) ρi BI hBI hcell hcBI
    rw [cN_unwind_iff hS, tabUN_eq_addImm hS δ Θ p α] at h2
    have h3 := erwp_tieEntry (Φ := Θ.view c) (Φ' := Θ'.view c) rfl
      (tabUN_abort hS δ Θ) (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact .inr (List.mem_cons_self ..)
        · exact .inl hy) h2
    -- step 7: the result returns to the world without the record
    refine erwp_mono_le k' (fun j hj ls' b ρ' hb => ?_) (fun j _ ls' t Ψ Ψ' ρ hΨ h =>
      opTableN_local T j ls' t Ψ Ψ' ρ hΨ h) k' le_rfl _ _ BI h3
    obtain ⟨β, hβ, hbB, hst⟩ := hb
    rw [interp_ext_self] at hβ
    cases Option.some.inj hβ
    refine ⟨fun Y X hY hX σ Z hσ hZ => ?_, hst⟩
    subst hY
    obtain ⟨Wc, hWc, hZ'⟩ :=
      (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf w₀)) σ Z).mpr ⟨X, hX, hZ⟩
    have hbB' : vN (ℍ := ℍ) B δ Θ j b ρ' := by
      rw [vN_extend_of_not_free hfree₂] at hbB
      exact vN_extR B δ j b ρ' (LocTy.extR_of_addImm Θ p hst) hbB
    exact ⟨Val.loc l, b, Wc, ρ', rfl, ResU.CompS.comm hZ', ⟨l, w₀, σ, rfl, hWc, vN_le hj hσ⟩,
      hbB'⟩

/-- `withbor1UD_sem` at `Σ_D = ∅`, `Σ_M = Σ`. -/
theorem withbor1U_sem {Δ : LifeCtx} {x : LifeVar} {A B : VTy} {S : Row} {d : Expr} {δ : LSub}
    (hδ : Δ.Models δ) (hadm : AdmWf A δ) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B)
    (hS : S.Unwind x) (Θ₀ : LocTy) (n : Nat)
    (hd : ∀ (Θ : LocTy), Θ.OK → ∀ c k, k ≤ n → ∀ ls,
      cN (ℍ := ℍ) (.ret (.lolli (.ref A) .unit)) δ Θ c k ls d PMap.empty) :
    vN (ℍ := ℍ) (withbor1UTy x Δ.meetOfDom A B S) δ Θ₀ n (withborUV d) PMap.empty :=
  withbor1UD_sem (SD := []) hδ hadm hfree₁ hfree₂ hS (RowLe.refl S) (RowLe.nil S)
    (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) Θ₀ n hd

/-- **`withbor1UD` at `SemJN`** (Core's `withbor1UD_compatX`): the callback at `Σ_M`, the
result at `Σ`, the finaliser at `Σ_D` (`withbor1UD_sem`).  `[spec §19, §27]` -/
theorem withbor1UD_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} {SM SD S : Row} {d : Expr}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A)
    (hfree₂ : ¬ VFree x B) (hS : SM.Unwind x) (hMS : RowLe SM S) (hDS : RowLe SD S)
    (hPend : SD.UnrD → SM.PendPers)
    (hd : SemJN (ℍ := ℍ) Δ Γ d (.val (.thunk (.arr (.ref A) (CTy.effOf SD .unit))))) :
    SemJN (ℍ := ℍ) Δ Γ (withborUE d) (.val (withbor1UTyD x Δ.meetOfDom A B SM S)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain rfl := gN_deadP hΓ hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ (withborUE d)) _
  rw [withborUE_psub γ d]
  refine erwp_val (v := withborUV (substAll γ d)) (withbor1UD_sem hδ (admWf_of_vScoped hsc₁ hδ) hfree₁ hfree₂
    hS hMS hDS hPend Θ n (fun Θ' hΘ' c' k hk ls' => ?_))
  have h := hd δ γ Θ' c' k ls' PMap.empty hδ hΘ' (consistentX_empty c') hlw
    (gN_dead_any hΓ hg Θ' k hk)
  exact h


/-- `withbor1UD_compatN` at `Σ_D = ∅`, `Σ_M = Σ`. -/
theorem withbor1U_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} {S : Row} {d : Expr}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A)
    (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
    (hd : SemJN (ℍ := ℍ) Δ Γ d (.val (.lolli (.ref A) .unit))) :
    SemJN (ℍ := ℍ) Δ Γ (withborUE d) (.val (withbor1UTy x Δ.meetOfDom A B S)) :=
  withbor1UD_compatN x hΓ hsc₁ hfree₁ hfree₂ hS (RowLe.refl S) (RowLe.nil S)
    (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) hd

/-! ### `withbor (2)` at an unwinding row -/

/-- **`withbor (2)` at an unwinding row is a value of its type**: `withborU d` at
`Ref A ⊸ (∀'x ⊏ @Δ. Mut 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ(Ref A ⊗ B)`, `Σ` a `Row.Unwind x` row. Core's
`withbor2U_compatX`, step by step, as `withbor2S_compat` with the bound `Δ.meetOfDom` defined at
`δ ⊨ Δ` and the row's table abortive: the lend at a lifetime fresh for the world, below the bound,
`[TR]` 6.60's stratum at the side condition `Δ ⊢ A ⊒ @b` and the callback's; the callback at the
world with the lend (`LocTy.view_add`); the Mut Frame across the row's raises (`erwp_M_frameR`,
Core's `ewpTS_M_frameU`); the claim consistent with the view (`erwp_claimX_abort`); the finaliser
frame at a raise (`erwp_ubindRaise`, `fin_claimI` at the claim's content). -/
theorem withbor2UD_sem {Δ : LifeCtx} {x : LifeVar} {A B : VTy} {SM SD S : Row} {d : Expr}
    {δ : LSub} (hδ : Δ.Models δ) (hO : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) (hA : ¬ VFree x A)
    (hB : ¬ VFree x B) (hS : SM.Unwind x) (hMS : RowLe SM S) (hDS : RowLe SD S)
    (hPend : SD.UnrD → SM.PendPers) (Θ₀ : LocTy) (n : Nat)
    (hd : ∀ (Θ : LocTy), Θ.OK → ∀ c k, k ≤ n → ∀ ls,
      cN (ℍ := ℍ) (.ret (.thunk (.arr (.ref A) (CTy.effOf SD .unit)))) δ Θ c k ls d PMap.empty) :
    vN (ℍ := ℍ) (withbor2UTyD x Δ.meetOfDom A B SM S) δ Θ₀ n (withborUV d) PMap.empty := by
  intro Θ _ hΘ c₁ _ ls c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  intro c k' hk' f ρf ρ'' hc' hf hcon
  obtain ⟨l, w₀, σ₀, rfl, hcl, hw₀⟩ := vN_le hk' hu
  refine (cN_effOf_tabF S _ δ Θ c k' ls _ ρ'').mpr fun lo => ?_
  rw [tabF_effOf_ret (rdN (ℍ := ℍ) δ) () S (.tensor (.ref A) B) .unit]
  refine erwpK_of_valid fun hv'' => ?_
  have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
  set T := tabUN (ℍ := ℍ) SM δ Θ with hTdef
  have hTd : T.Down := tabUN_down SM δ Θ
  have hQo : ∀ y : KW, PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) (.tensor (.ref A) B) δ y.Θ k v ρ) :=
    fun y k _ v ρ h => vN_down _ δ y.Θ k v ρ h
  have hTo := opTableK_downI (lo := lo) (tabF_downI (rdN_ok (ℍ := ℍ) δ) () (CTy.effOf S .unit)
    (⟨Θ, c, lo⟩ : KW))
  refine erwpK_det (x := (⟨Θ, c, lo⟩ : KW)) hΦ hTo hQo
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl (.appL .hole f)) ?_
  refine erwpK_det (x := (⟨Θ, c, lo⟩ : KW)) hΦ hTo hQo
    (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 f (Expr.subst (0 + 1) (Val.shift 1 0 (Val.loc l))
        (thenE ((Expr.var 2).pair (Expr.var 0)) ((d.shift 3 0).app (Expr.var 2))
          (((Expr.var 0).app (Expr.val Val.unit)).app (Expr.var 1))))) =
      ubindE (.pair (NFv l) (DFv (d.shift 1 0) l)) (.app (.app (.val f) (.val .unit)) (.val (Val.loc l))) := by
    simp [Kont.plug, Expr.subst, Expr.shift, thenE, ubindE, NFv, DFv, Val.shift, Val.pair,
      Val.loc, Val.lam, Expr.val, Val.prim, subst_shift_succ (j := 2) (d := 2) _ d (le_refl _),
      subst_shift_succ (j := 1) (d := 1) _ d (le_refl _)]
  rw [e₃]
  have hvu : ResU.Valid ρu := (ResU.Valid.split hc' hv'').1
  have hcf : ConsistentX c ρf := consistentX_right hc' hcon hv''
  have hcσ : ConsistentX c σ₀ := consistentX_right hcl (consistentX_left hc' hcon hv'') hvu
  have hko : (CellU.ownOf (Loc := Loc) w₀).kind ≠ Kind.imm := by simp
  have hown : ρu.get l = some (CellU.ownOf w₀) :=
    (ResU.CompS.get_left_of_ne_imm hcl (ResU.single_get_self _ _) hko).2
  -- the lend's lifetime
  obtain ⟨γ, hγ⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  obtain ⟨b, hdef, hOb⟩ := hO
  obtain ⟨βP, hβP⟩ : ∃ β : Life, b.interp δ = some β := hdef δ hδ
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  obtain ⟨α, hαle, hfr⟩ := LocTy.exists_fresh hΘ.2 (↓(βP ⊓ βf ⊓ γ))
  have hαlt : α < βP ⊓ βf ⊓ γ := lt_of_le_of_lt hαle (Life.down_sqsubset _)
  have hαP : α < βP := lt_of_lt_of_le hαlt (inf_le_left.trans inf_le_left)
  have hunif : ∀ (Θ' : LocTy) (j : Nat) (u : Val) (r : WRes), vN (ℍ := ℍ) A δ Θ' j u r →
      r.InStratum α :=
    vN_outlivesLe hδ hβP hαP hOb
  have houtP : σ₀.InStratum α := hunif Θ k' w₀ σ₀ hw₀
  have houtf : ρf.InStratum (↓α) := hβf.mono
    ((Life.down_sqsubset α).le.trans (hαlt.le.trans (inf_le_left.trans inf_le_right)))
  have hLt : LtLife δ Δ.meetOfDom α := ⟨γ, hγ, lt_of_lt_of_le hαlt inf_le_right⟩
  set δ' := δ.extend x α with hδ'
  have hAδ : vN (ℍ := ℍ) A δ' = vN (ℍ := ℍ) A δ := vN_extend_of_not_free hA δ α
  have hBδ : vN (ℍ := ℍ) B δ' = vN (ℍ := ℍ) B δ := vN_extend_of_not_free hB δ α
  set P : CPredL := fun Θ' j u r => vN (ℍ := ℍ) A δ' Θ' j u r with hP
  set Fam : Nat → Val → SPropS Loc Val α := famL α P Θ with hFam
  have hFamD : DownFam α Fam := vN_fam_down A δ' α Θ
  have hwit : Fam k' w₀ ⟨σ₀, houtP⟩ := (vN_above A δ' Θ houtP).mpr (by rw [hAδ]; exact hw₀)
  -- the callback's world and view
  set Θ' := Θ.add l α Fam with hΘ'
  set c' := setLife c l α with hc'def
  have hOK' : Θ'.OK := by
    obtain ⟨N, hN⟩ := hΘ.2
    exact ⟨LocTy.down_add hΘ.1 l hFamD, ⟨min N (↓α), LocTy.fresh_add hN (min_le_left _ _)
      (lt_of_le_of_lt (min_le_right _ _) (Life.down_sqsubset α)) l Fam⟩⟩
  have hview : Θ'.view c' = (Θ.view c).set l α Fam := LocTy.view_add Θ c l α Fam
  have hcf' : ConsistentX c' ρf := consistentX_setLife hcf (exS_none_of_part hc' hv'' hown hko) α
  have hcσ' : ConsistentX c' σ₀ :=
    consistentX_setLife hcσ (exS_none_of_part hcl hvu (ResU.single_get_self _ _) hko) α
  set Qb : PostN := fun k _ b ρ => vN (ℍ := ℍ) (.tensor (.ref A) B) δ Θ k
    (Val.pair (Val.loc l) b) ρ with hQb
  have hM := erwp_M_frameR (Φ := Θ.view c) (l := l) (A := α) (F := Fam) hFamD
    (tabUN_lendOKR hS δ Θ α) (Q := Qb)
    k' k' le_rfl ls (.app (.app (.val f) (.val .unit)) (.val (Val.loc l))) w₀ σ₀ ρu ρf ρ''
    houtP houtf (Fam k') (fun _ _ h => h) hwit hcl hc' (fun BM hBM => ?_)
  · -- the claim with the view's consistency, then the finaliser frame
    have hM' := erwp_claimX_abort (tabUN_abort hS δ Θ) hcon hM
    have hM'' := erwp_mono_le
      (Tb' := opTableR T (fun j ρ => claimX (claimR l α Fam) c j ρ ∧ j ≤ k')) k'
      (fun _ _ _ _ _ h => h) (fun j hj ls' t Ψ Ψ' ρ hΨ h => by
        rcases h with ⟨K, m, i, v, en, h⟩ | ⟨K, m, i, v, en, h⟩
        · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp h
          exact absurd ha (by rw [tabUN_abort hS δ Θ m i en hTe]; decide)
        · obtain ⟨hp, τ, τR, hcτ, h₁, hR⟩ := pure_sep_iff.mp h
          exact Or.inr ⟨K, m, i, v, en, pure_sep_mk hp ⟨τ, τR, hcτ, h₁, hR, hj⟩⟩)
      k' le_rfl ls _ ρ'' hM'
    refine erwpK_unwindD (R := rdN (ℍ := ℍ) δ) (rdN_ok δ) (rdN_payExt δ) S SD hDS (μ := ())
      (T := T) (tabUN_abort hS δ Θ)
      (fun m i en h => tabUN_named hS δ Θ m i en h (tabUN_abort hS δ Θ m i en h))
      (x := (⟨Θ, c, lo⟩ : KW)) hΘ.1 ?_ (NFv l) (DFv (d.shift 1 0) l)
      (Qd := fun z k _ v ρ => vN (ℍ := ℍ) .unit δ z.Θ k v ρ) ?_ hQo k' ?_ ?_ ls _ ρ'' hM''
    · -- the raise's entry, read in `Σ`
      intro m i en h
      obtain ⟨o, hf, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨o', hf', hle⟩ := hMS m i o hf
      have hab : o.abort = true := (hS o (Row.find_mem hf).1).1
      refine ⟨o', hf', by rw [← hle.1.abort_eq]; exact hab, fun hu => ?_, fun k ls v ρ hp => ?_⟩
      · have h₁ := ((hPend hu) o (Row.find_mem hf).1).1 hab
        rwa [hle.1.2.2.2.1] at h₁
      · show vN (ℍ := ℍ) o'.A δ Θ k v ρ
        rw [← hle.1.2.2.2.1]; exact hp
    · rintro y k ls' v σ ⟨rfl, rfl⟩
      exact ⟨rfl, noOwn_empty⟩
    · -- the finaliser at `Σ_D`, from the claim
      intro j hj ls' ρ hR
      obtain ⟨⟨⟨w, σ, hσ, hF, hclm⟩, hcR⟩, -⟩ := hR
      have hwσ : vN (ℍ := ℍ) A δ Θ j w σ := by rw [← hAδ]; exact (vN_above A δ' Θ hσ).mp hF
      exact fin_claimID hΘ lo
        (fun j' hj' ls => hd Θ hΘ c j' (hj'.trans (hj.trans (hk'.trans hk))) ls) hwσ le_rfl hclm hcR
    · -- a return: `(ℓ, b)` at the world `⟨Θ, c, lo⟩`
      intro j _ ls' b ρ hq
      refine erwpK_det (x := (⟨Θ, c, lo⟩ : KW)) hΦ hTo hQo
        (fun μ => step1Only_plug (Head.beta μ _ b) rfl .hole) ?_
      simp [Kont.plug, Expr.subst]
      exact erwpK_val (v := Val.pair (Val.loc l) b) (KW.postK_refl _) hq
  · -- the callback, at the lend's world and view, from the borrow
    rw [← hview]
    have h1 := (hf Θ' ((LocTy.extA_add hfr l Fam).extR ρf) hOK' c' hcf' ls) α hLt
    have hcell : vN (ℍ := ℍ) (.mut (.var x) A) δ' Θ' k' (Val.loc l)
        (ResU.single l (CellU.mutOf α w₀ σ₀ houtP (Fam k') hwit)) :=
      ⟨α, interp_ext_self δ x α, α, le_rfl, lend_mutL Θ l α P le_rfl houtP hwit,
        fun Θ'' j u r h => hunif Θ'' j u r (by rw [← hAδ]; exact h)⟩
    have hcBM : ConsistentX c' BM := consistentX_compS hBM hcf'
      (consistentX_single_mut hcσ' (by simp [hc'def, setLife]))
    have h2 := h1 c' k' le_rfl (Val.loc l) _ BM hBM hcell hcBM
    rw [cN_unwind_iff hS, tabUN_eq_add hS δ hfr l Fam] at h2
    refine erwp_mono (fun k ls' b ρ' hb => ?_) (opTableN_local _) k' ls _ BM h2
    obtain ⟨β, hβ, hbB, hst⟩ := hb
    rw [interp_ext_self] at hβ
    cases Option.some.inj hβ
    refine ⟨hst, fun w Y hY σ ⟨hσ, hFσ⟩ Z hZ => ?_⟩
    obtain ⟨Wc, hWc, hZ'⟩ :=
      (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf w)) σ Z).mpr ⟨Y, hY, hZ⟩
    have hwσ : vN (ℍ := ℍ) A δ Θ k w σ := by
      rw [← hAδ]; exact (vN_above A δ' Θ hσ).mp hFσ
    have hbB' : vN (ℍ := ℍ) B δ Θ k b ρ' :=
      vN_local B δ Θ l α Fam k b ρ' hst (by rw [← hBδ]; exact hbB)
    exact ⟨Val.loc l, b, Wc, ρ', rfl, ResU.CompS.comm hZ', ⟨l, w, σ, rfl, hWc, hwσ⟩, hbB'⟩

/-- `withbor2UD_sem` at `Σ_D = ∅`, `Σ_M = Σ`. -/
theorem withbor2U_sem {Δ : LifeCtx} {x : LifeVar} {A B : VTy} {S : Row} {d : Expr} {δ : LSub}
    (hδ : Δ.Models δ) (hO : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) (hA : ¬ VFree x A)
    (hB : ¬ VFree x B) (hS : S.Unwind x) (Θ₀ : LocTy) (n : Nat)
    (hd : ∀ (Θ : LocTy), Θ.OK → ∀ c k, k ≤ n → ∀ ls,
      cN (ℍ := ℍ) (.ret (.lolli (.ref A) .unit)) δ Θ c k ls d PMap.empty) :
    vN (ℍ := ℍ) (withbor2UTy x Δ.meetOfDom A B S) δ Θ₀ n (withborUV d) PMap.empty :=
  withbor2UD_sem (SD := []) hδ hO hA hB hS (RowLe.refl S) (RowLe.nil S)
    (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) Θ₀ n hd

/-- **`withbor2UD` at `SemJN`** (Core's `withbor2UD_compatX`): the callback at `Σ_M`, the
result at `Σ`, the finaliser at `Σ_D` (`withbor2UD_sem`).  `[spec §19, §27]` -/
theorem withbor2UD_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} {SM SD S : Row} {d : Expr}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : SM.Unwind x) (hMS : RowLe SM S) (hDS : RowLe SD S)
    (hPend : SD.UnrD → SM.PendPers)
    (hd : SemJN (ℍ := ℍ) Δ Γ d (.val (.thunk (.arr (.ref A) (CTy.effOf SD .unit))))) :
    SemJN (ℍ := ℍ) Δ Γ (withborUE d) (.val (withbor2UTyD x Δ.meetOfDom A B SM S)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain rfl := gN_deadP hΓ hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ (withborUE d)) _
  rw [withborUE_psub γ d]
  refine erwp_val (v := withborUV (substAll γ d)) (withbor2UD_sem hδ hside hfree₁ hfree₂ hS hMS hDS hPend Θ n
    (fun Θ' hΘ' c' k hk ls' => ?_))
  have h := hd δ γ Θ' c' k ls' PMap.empty hδ hΘ' (consistentX_empty c') hlw
    (gN_dead_any hΓ hg Θ' k hk)
  exact h


/-- `withbor2UD_compatN` at `Σ_D = ∅`, `Σ_M = Σ`. -/
theorem withbor2U_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} {S : Row} {d : Expr}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
    (hd : SemJN (ℍ := ℍ) Δ Γ d (.val (.lolli (.ref A) .unit))) :
    SemJN (ℍ := ℍ) Δ Γ (withborUE d) (.val (withbor2UTy x Δ.meetOfDom A B S)) :=
  withbor2UD_compatN x hΓ hside hfree₁ hfree₂ hS (RowLe.refl S) (RowLe.nil S)
    (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) hd

/-! ### An unwinding row's table under a reborrow -/

/-- **An unwinding row's table may be stopped at under a `mut` lend at any `α`, cancellable stops
included**. -/
theorem tabUN_lendOKCR {S : Row} {x : LifeVar} (hS : S.Unwind x) (δ : LSub) (Θ : LocTy)
    (α : Life) : (tabUN (ℍ := ℍ) S δ Θ).LendOKCR α where
  entry := fun m i en h ha => by
    rw [tabUN_abort hS δ Θ m i en h] at ha; cases ha
  pa := (tabUN_lendOKR hS δ Θ α).pa
  pb := (tabUN_lendOKR hS δ Θ α).pb

/-- **An unwinding row's table may be stopped at under a reborrow at any `β`** -/
theorem tabUN_rebOKR {S : Row} {x : LifeVar} (hS : S.Unwind x) (δ : LSub) (Θ : LocTy)
    (β : Life) : (tabUN (ℍ := ℍ) S δ Θ).RebOKR β where
  entry := fun m i en h ha => by
    rw [tabUN_abort hS δ Θ m i en h] at ha; cases ha
  pa := (tabUN_lendOKR hS δ Θ β).pa
  pb := fun m i en h k ls w ρ hp => by
    obtain ⟨o, ho, -, rfl⟩ := tabUN_some h
    exact hp.elim

/-- **An unwinding row's table has no cancel obligation**. -/
theorem tabUN_rebClosed {S : Row} {x : LifeVar} (hS : S.Unwind x) (δ : LSub) (Θ : LocTy)
    (β : Life) (ρi χ : WRes) (Ok : List SRec → Prop) :
    RebClosed β ρi χ Ok (tabUN (ℍ := ℍ) S δ Θ) := by
  intro m i en h ha
  rw [tabUN_abort hS δ Θ m i en h] at ha; cases ha

/-- **An unwinding row's table does not read `'x`**. -/
theorem tabUN_extend {S : Row} {x : LifeVar} (hS : S.Unwind x) (δ : LSub) (Θ : LocTy)
    (α : Life) : tabUN (ℍ := ℍ) S (δ.extend x α) Θ = tabUN (ℍ := ℍ) S δ Θ :=
  tabUN_congr fun o ho => by rw [vN_extend_of_not_free (hS o ho).2.2.1 δ α]

/-! ### `withbor (3)` at an unwinding row -/

/-- **The finaliser `λ_. d ℓ` consumes a `Mut @a A` source**, `d`'s judgment at `Mut @a A ⊸ 1`
read at the world and an index at or below `N` (`fin_claimM` with the judgment at the run's
world). -/
theorem fin_claimMN {a : Lifetime.Life} {A : VTy} {d : Expr}
    {δ : LSub} {Θ : LocTy} (hΘ : Θ.OK) {c : Loc → Option Life} {N : Nat}
    (hd : ∀ k, k ≤ N → ∀ ls,
      cN (ℍ := ℍ) (.ret (.lolli (.mut a A) .unit)) δ Θ c k ls d PMap.empty)
    {l : Loc} {k : Nat} (hk : k ≤ N) {ls : List SRec} {ρ : WRes}
    (h : vN (ℍ := ℍ) (.mut a A) δ Θ k (Val.loc l) ρ) (hc : ConsistentX c ρ) :
    rwp (ℍ := ℍ) (Θ.view c) (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
      (.app (.val (DFv (d.shift 1 0) l)) (.val .unit)) ρ := by
  have hΦ := LocTy.view_down hΘ.1 c
  refine Hardest791.rwp_det'' (Q := fun _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) hΦ
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (.app (d.shift 1 0) (.val (Val.loc l)))) =
      (Kont.appL .hole (Val.loc l)).plug d := by
    simp [Kont.plug, Expr.subst, subst_shift_succ (j := 0) (d := 0) _ d (le_refl _), Expr.shift_zero, Val.loc]
  rw [e]
  refine rwp_bind hΦ _ ?_
  have hd0 := hd k hk ls
  have hfr := rwp_frame (fun _ τ => τ = ρ) (fun _ _ _ _ h => h) (compS_empty_left ρ)
    (rwp_of_erwp_empty (erwp_of_cN_ret hd0)) rfl
  refine rwp_mono_le (fun k' hk' ls' v τ hv => ?_) (rwp_consistentXV hfr hc)
  obtain ⟨⟨τ₁, τ₂, hcτ, hP, rfl⟩, hcτ', hvτ⟩ := hv
  have := hP Θ (LocTy.extR_refl Θ _) hΘ c (consistentX_left hcτ hcτ' hvτ) ls'
    c k' le_rfl (Val.loc l) τ₂ τ hcτ (vN_le hk' h) hcτ'
  exact rwp_of_erwp_empty (erwp_of_cN_ret this)

/-- **`withbor (3)` at an unwinding row is a value of its type**: `withborU d`, at
`Mut @a A ⊸ (∀'x ⊏ @Δ. Mut 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ(Mut @a A ⊗ B)` with `Σ` a `Row.Unwind x`
row. Core's `withbor3U_compatX`, step by step, as `withbor3S_compat`:

1. the source is `loc ℓ` with its cell `ℓ ↦ mut(β, w₀, σ₀, F_o j₀)`, `F_o = famL β 𝒱⟦A⟧ Θ`;
2. `withborU d ℓ f` steps to the callback under the finaliser frame `then b. (ℓ, b) unwind d ℓ`;
3. `MutFrame`'s premise read off the borrow: every value of `A` is in `Res_β` (`hunif`);
4. the anti-frame at the source's own entry: `c ℓ = β` (`consistentX_get`) and the view types
   `ℓ` with `F_o` (`reseal_at_entry`);
5. the opened cell lent at a fresh `α` below `β`, the bound `Δ.meetOfDom` and the callback's
   stratum (`erwp_M_frameCRG` at the row's table, `tabUN_lendOKCR`), the anti-frame across
   the row's raises (`erwp_M_antiFrameU`, Core's `ewpTS_M_antiFrameU`);
6. the callback at the world `Θ + (ℓ, α) ↦ famL α 𝒱⟦A⟧ Θ` and the view `setLife c ℓ α`, its table
   the lender's (`tabUN_eq_add`), from the borrow `Mut @α A` (`lend_mutL`);
7. its result `['x] B` back at `Θ` (`vN_local`); the content handed back in `F_i k` is in `F_o k`
   (`hunif`, `vN_above`), and the resealed cell is a `Mut @a A` value again, beside the result and
   in every raise's claim;
8. the claim consistent with the view (`erwp_claimX_abort`) and the finaliser frame consuming it
   with `d` (`erwp_ubindRaise`, `fin_claimMN`).

Premises: `hδ`, `hA`, `hB`, `hS` are the rule's; `hd` is the finaliser's judgment at the
run's world and every lower index. -/
theorem withbor3UD_sem {Δ : LifeCtx} {a : Lifetime.Life} {x : LifeVar} {A B : VTy} {SM SD S : Row}
    {d : Expr} {δ : LSub} (hδ : Δ.Models δ) (hA : ¬ VFree x A) (hB : ¬ VFree x B)
    (hS : SM.Unwind x) (hMS : RowLe SM S) (hDS : RowLe SD S)
    (hPend : SD.UnrD → SM.PendPers) (Θ₀ : LocTy) (n : Nat)
    (hd : ∀ (Θ : LocTy), Θ.OK → ∀ c k, k ≤ n → ∀ ls,
      cN (ℍ := ℍ) (.ret (.thunk (.arr (.mut a A) (CTy.effOf SD .unit)))) δ Θ c k ls d PMap.empty) :
    vN (ℍ := ℍ) (withbor3UTyD a x Δ.meetOfDom A B SM S) δ Θ₀ n (withborUV d) PMap.empty := by
  intro Θ _ hΘ c₁ _ ls c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  intro c k' hk' f ρf ρ'' hc' hf hcon
  set P : CPredL := fun Θ' j u r => vN (ℍ := ℍ) A δ Θ' j u r with hP
  -- step 1
  obtain ⟨α₀, hα₀, (β : Life), hα₀β, hm, hunif⟩ := vN_le hk' hu
  obtain ⟨l, w₀, σ₀, hσ₀, j₀, hw₀, hkj, rfl, hl, rfl⟩ := id hm
  refine (cN_effOf_tabF S _ δ Θ c k' ls _ ρ'').mpr fun lo => ?_
  rw [tabF_effOf_ret (rdN (ℍ := ℍ) δ) () S (.tensor (.mut a A) B) .unit]
  refine erwpK_of_valid fun hv'' => ?_
  have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
  set T := tabUN (ℍ := ℍ) SM δ Θ with hTdef
  have hTd : T.Down := tabUN_down SM δ Θ
  have hab : ∀ m i en, T m i = some en → en.abort = true := tabUN_abort hS δ Θ
  have hQo : ∀ y : KW, PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) (.tensor (.mut a A) B) δ y.Θ k v ρ) :=
    fun y k _ v ρ h => vN_down _ δ y.Θ k v ρ h
  have hTo := opTableK_downI (lo := lo) (tabF_downI (rdN_ok (ℍ := ℍ) δ) () (CTy.effOf S .unit)
    (⟨Θ, c, lo⟩ : KW))
  set Qin : PostN := fun k _ b ρ =>
    vN (ℍ := ℍ) (.tensor (.mut a A) B) δ Θ k (Val.pair (Val.loc l) b) ρ with hQin
  -- step 2
  refine erwpK_det (x := (⟨Θ, c, lo⟩ : KW)) hΦ hTo hQo
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl (.appL .hole f)) ?_
  refine erwpK_det (x := (⟨Θ, c, lo⟩ : KW)) hΦ hTo hQo
    (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 f (Expr.subst (0 + 1) (Val.shift 1 0 (Val.loc l))
        (thenE ((Expr.var 2).pair (Expr.var 0)) ((d.shift 3 0).app (Expr.var 2))
          (((Expr.var 0).app (Expr.val Val.unit)).app (Expr.var 1))))) =
      ubindE (.pair (NFv l) (DFv (d.shift 1 0) l)) (.app (.app (.val f) (.val .unit)) (.val (Val.loc l))) := by
    simp [Kont.plug, Expr.subst, Expr.shift, thenE, ubindE, NFv, DFv, Val.shift, Val.pair,
      Val.loc, Val.lam, Expr.val, Val.prim, subst_shift_succ (j := 2) (d := 2) _ d (le_refl _),
      subst_shift_succ (j := 1) (d := 1) _ d (le_refl _)]
  rw [e₃]
  -- the source's cell
  set cellβ := ResU.single l (CellU.mutOf β w₀ σ₀ hσ₀ (famL β P Θ j₀) hw₀) with hcellβ
  have hvu : ResU.Valid cellβ := (ResU.Valid.split hc' hv'').1
  have hkm : (CellU.mutOf β w₀ σ₀ hσ₀ (famL β P Θ j₀) hw₀).kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hget : ρ''.get l = some (CellU.mutOf β w₀ σ₀ hσ₀ (famL β P Θ j₀) hw₀) :=
    (ResU.CompS.get_left_of_ne_imm hc' (ResU.single_get_self _ _) hkm).2
  -- step 4
  have hcl : c l = some β := by
    have h := consistentX_get hcon hv'' hget (CellU.kind_mutOf _ _ _ _ _ _)
    rwa [CellU.at_mutOf] at h
  obtain ⟨-, -, -, -, -, -, -, hFv, -⟩ :=
    reseal_at_entry (Θ' := Θ) (fun _ _ _ h => h) hcl (vN_fam_down A δ β Θ) hm
  have hcf : ConsistentX c ρf := consistentX_right hc' hcon hv''
  have hcσ : ConsistentX c σ₀ := consistentX_mut_wit (consistentX_left hc' hcon hv'') hvu
  -- steps 3 and 5: the lend's lifetime, fresh, below `β`, the bound and the callback's stratum
  obtain ⟨γ, hγ⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  obtain ⟨α, hαle, hfr⟩ := LocTy.exists_fresh hΘ.2 (↓(β ⊓ βf ⊓ γ))
  have hαlt : α < β ⊓ βf ⊓ γ := lt_of_le_of_lt hαle (Life.down_sqsubset _)
  have hαβ : α ≤ β := hαlt.le.trans (inf_le_left.trans inf_le_left)
  have houtP : σ₀.InStratum α := hσ₀.mono hαβ
  have houtf : ρf.InStratum (↓α) := hβf.mono
    ((Life.down_sqsubset α).le.trans (hαlt.le.trans (inf_le_left.trans inf_le_right)))
  have hLt : LtLife δ Δ.meetOfDom α := ⟨γ, hγ, lt_of_lt_of_le hαlt inf_le_right⟩
  set δ' := δ.extend x α with hδ'
  have hAδ : vN (ℍ := ℍ) A δ' = vN (ℍ := ℍ) A δ := vN_extend_of_not_free hA δ α
  have hBδ : vN (ℍ := ℍ) B δ' = vN (ℍ := ℍ) B δ := vN_extend_of_not_free hB δ α
  set P' : CPredL := fun Θ' j u r => vN (ℍ := ℍ) A δ' Θ' j u r with hP'
  set Fam : Nat → Val → SPropS Loc Val α := famL α P' Θ with hFam
  have hFamD : DownFam α Fam := vN_fam_down A δ' α Θ
  have hwit : Fam j₀ w₀ ⟨σ₀, houtP⟩ :=
    (vN_above A δ' Θ houtP).mpr (by rw [hAδ]; exact (vN_above A δ Θ hσ₀).mp hw₀)
  -- step 7's inclusion: the content handed back in `F_i k` is in `F_o k`
  have hoi : ∀ k w σ (h : σ.InStratum α), Fam k w ⟨σ, h⟩ →
      ∃ h' : σ.InStratum β, famL β P Θ k w ⟨σ, h'⟩ := by
    intro k w σ h hw
    have hv : vN (ℍ := ℍ) A δ Θ k w σ := by rw [← hAδ]; exact (vN_above A δ' Θ h).mp hw
    exact ⟨hunif Θ k w σ hv, (vN_above A δ Θ (hunif Θ k w σ hv)).mpr hv⟩
  have hG : ∀ k ls ρ, CellFold l α Fam k ls ρ → CellFold l β (famL β P Θ) k ls ρ := by
    rintro k ls ρ ⟨w, χ, h, hw, R, rest, h1, h2⟩
    obtain ⟨h', hw'⟩ := hoi k w χ h hw
    exact ⟨w, χ, h', hw', R, rest, h1, h2⟩
  have hRin : ∀ k ρ, claimR l α Fam k ρ → claimR l β (famL β P Θ) k ρ := by
    rintro k ρ ⟨w, σ, h, hw, hcl'⟩
    obtain ⟨h', hw'⟩ := hoi k w σ h hw
    exact ⟨w, σ, h', hw', hcl'⟩
  set Rout : Nat → WProp := fun k ρ => vN (ℍ := ℍ) (.mut a A) δ Θ k (Val.loc l) ρ with hRoutd
  have hRout : ∀ k (w : Val) (σ : WRes) (h : σ.InStratum β) (hw : famL β P Θ k w ⟨σ, h⟩),
      Rout k (ResU.single l (CellU.mutOf β w σ h (famL β P Θ k) hw)) :=
    fun k w σ h hw => ⟨α₀, hα₀, β, hα₀β, ⟨l, w, σ, h, k, hw, le_rfl, rfl, hl, rfl⟩, hunif⟩
  -- step 6: the callback's world and view
  set Θ' := Θ.add l α Fam with hΘ'
  set c' := setLife c l α with hc'def
  have hOK' : Θ'.OK := by
    obtain ⟨N, hN⟩ := hΘ.2
    exact ⟨LocTy.down_add hΘ.1 l hFamD, ⟨min N (↓α), LocTy.fresh_add hN (min_le_left _ _)
      (lt_of_le_of_lt (min_le_right _ _) (Life.down_sqsubset α)) l Fam⟩⟩
  have hview : Θ'.view c' = (Θ.view c).set l α Fam := LocTy.view_add Θ c l α Fam
  have hcf' : ConsistentX c' ρf :=
    consistentX_setLife hcf (exS_none_of_part hc' hv'' (ResU.single_get_self _ _) hkm) α
  have hcσ' : ConsistentX c' σ₀ := consistentX_setLife hcσ (exS_wit_none hvu) α
  -- step 5: the anti-frame at the source, across the row's raises
  have hAF := erwp_M_antiFrameU (Φ := Θ.view c) hΦ hFv hab hG hRin hRout (Q := Qin) k' ls
    (.app (.app (.val f) (.val .unit)) (.val (Val.loc l))) w₀ σ₀ hσ₀ j₀ hw₀ ρf ρ'' hc'
    (fun W X hW hX => ?_)
  · -- step 8: the claim consistent, the finaliser frame consuming it
    have hM' := erwp_claimX_abort hab hcon hAF
    have hM'' := erwp_mono_le
      (Tb' := opTableR T (fun j ρ => claimX Rout c j ρ ∧ j ≤ k')) k'
      (fun _ _ _ _ _ h => h) (fun j hj ls' t Ψ Ψ' ρ hΨ h => by
        rcases h with ⟨K, m, i, v, en, h⟩ | ⟨K, m, i, v, en, h⟩
        · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp h
          exact absurd ha (by rw [hab m i en hTe]; decide)
        · obtain ⟨hp, τ, τR, hcτ, h₁, hR⟩ := pure_sep_iff.mp h
          exact Or.inr ⟨K, m, i, v, en, pure_sep_mk hp ⟨τ, τR, hcτ, h₁, hR, hj⟩⟩)
      k' le_rfl ls _ ρ'' hM'
    refine erwpK_unwindD (R := rdN (ℍ := ℍ) δ) (rdN_ok δ) (rdN_payExt δ) S SD hDS (μ := ())
      (T := T) (tabUN_abort hS δ Θ)
      (fun m i en h => tabUN_named hS δ Θ m i en h (tabUN_abort hS δ Θ m i en h))
      (x := (⟨Θ, c, lo⟩ : KW)) hΘ.1 ?_ (NFv l) (DFv (d.shift 1 0) l)
      (Qd := fun z k _ v ρ => vN (ℍ := ℍ) .unit δ z.Θ k v ρ) ?_ hQo k' ?_ ?_ ls _ ρ'' hM''
    · -- the raise's entry, read in `Σ`
      intro m i en h
      obtain ⟨o, hf, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨o', hf', hle⟩ := hMS m i o hf
      have hab' : o.abort = true := (hS o (Row.find_mem hf).1).1
      refine ⟨o', hf', by rw [← hle.1.abort_eq]; exact hab', fun hu => ?_, fun k ls v ρ hp => ?_⟩
      · have h₁ := ((hPend hu) o (Row.find_mem hf).1).1 hab'
        rwa [hle.1.2.2.2.1] at h₁
      · show vN (ℍ := ℍ) o'.A δ Θ k v ρ
        rw [← hle.1.2.2.2.1]; exact hp
    · rintro y k ls' v σ ⟨rfl, rfl⟩
      exact ⟨rfl, noOwn_empty⟩
    · -- the finaliser at `Σ_D`, from the claim
      intro j hj ls' ρ hR
      obtain ⟨⟨hRj, hcR⟩, hj'⟩ := hR
      exact fin_claimMD hΘ lo
        (fun j' hj'' ls => hd Θ hΘ c j' (hj''.trans (hj'.trans (hk'.trans hk))) ls) le_rfl hRj hcR
    · -- a return: `(ℓ, b)` at the world `⟨Θ, c, lo⟩`
      intro j _ ls' b ρ hq
      refine erwpK_det (x := (⟨Θ, c, lo⟩ : KW)) hΦ hTo hQo
        (fun μ => step1Only_plug (Head.beta μ _ b) rfl .hole) ?_
      simp [Kont.plug, Expr.subst]
      exact erwpK_val (v := Val.pair (Val.loc l) b) (KW.postK_refl _) hq
  -- step 5: the opened cell lent at `α`, at the row's table
  refine erwp_M_frameCRG (Φ := Θ.view c) (l := l) (A := α) (F := Fam) hFamD
    (tabUN_lendOKCR hS δ Θ α) (OpTabN.Twin.refl T)
    (fun m i en _ h _ ha => by rw [hab m i en h] at ha; cases ha)
    (Q := AFPost l β (famL β P Θ) Qin)
    k' j₀ hkj ls _ w₀ σ₀ W ρf X houtP houtf (Fam j₀) (fun _ _ h => h) hwit
    (ResU.CompS.comm hW) (ResU.CompS.comm hX) (fun BM hBM => ?_)
  -- step 6: the callback, at the lend's world and view, from the borrow
  rw [← hview]
  have h1 := (hf Θ' ((LocTy.extA_add hfr l Fam).extR ρf) hOK' c' hcf' ls) α hLt
  have hcell : vN (ℍ := ℍ) (.mut (.var x) A) δ' Θ' k' (Val.loc l)
      (ResU.single l (CellU.mutOf α w₀ σ₀ houtP (Fam j₀) hwit)) :=
    ⟨α, interp_ext_self δ x α, α, le_rfl, lend_mutL Θ l α P' hkj houtP hwit,
      fun Θ'' j u r h => (hunif Θ'' j u r (by rw [← hAδ]; exact h)).mono hαβ⟩
  have hcBM : ConsistentX c' BM := consistentX_compS hBM hcf'
    (consistentX_single_mut hcσ' (by simp [hc'def, setLife]))
  have h2 := h1 c' k' le_rfl (Val.loc l) _ BM hBM hcell hcBM
  rw [cN_unwind_iff hS, tabUN_eq_add hS δ hfr l Fam] at h2
  refine erwp_mono (fun k ls' b ρ' hb => ?_) (opTableN_local _) k' ls _ BM h2
  obtain ⟨β', hβ', hbB, hst⟩ := hb
  rw [interp_ext_self] at hβ'
  cases Option.some.inj hβ'
  refine ⟨hst, fun w Y hY σ ⟨hσ, hFσ⟩ Z hZ => ?_⟩
  -- step 7: the result back at `Θ`, the content in `F_o k`, the cell resealed
  obtain ⟨h', hw'⟩ := hoi k w σ hσ hFσ
  obtain ⟨ac, hac, hacZ⟩ := compS_exch hY hZ
  have hbB' : vN (ℍ := ℍ) B δ Θ k b ρ' :=
    vN_local B δ Θ l α Fam k b ρ' hst (by rw [← hBδ]; exact hbB)
  exact ⟨w, σ, h', hw', ρ', ac, ResU.CompS.comm hacZ, ResU.CompS.comm hac, fun X' hX' =>
    ⟨Val.loc l, b, _, ρ', rfl, ResU.CompS.comm hX', hRout k w σ h' hw', hbB'⟩⟩

/-- `withbor3UD_sem` at `Σ_D = ∅`, `Σ_M = Σ`. -/
theorem withbor3U_sem {Δ : LifeCtx} {a : Lifetime.Life} {x : LifeVar} {A B : VTy} {S : Row}
    {d : Expr} {δ : LSub} (hδ : Δ.Models δ) (hA : ¬ VFree x A) (hB : ¬ VFree x B)
    (hS : S.Unwind x) (Θ₀ : LocTy) (n : Nat)
    (hd : ∀ (Θ : LocTy), Θ.OK → ∀ c k, k ≤ n → ∀ ls,
      cN (ℍ := ℍ) (.ret (.lolli (.mut a A) .unit)) δ Θ c k ls d PMap.empty) :
    vN (ℍ := ℍ) (withbor3UTy a x Δ.meetOfDom A B S) δ Θ₀ n (withborUV d) PMap.empty :=
  withbor3UD_sem (SD := []) hδ hA hB hS (RowLe.refl S) (RowLe.nil S)
    (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) Θ₀ n hd

/-- **`withbor3UD` at `SemJN`** (Core's `withbor3UD_compatX`): the callback at `Σ_M`, the
result at `Σ`, the finaliser at `Σ_D` (`withbor3UD_sem`).  `[spec §19, §27]` -/
theorem withbor3UD_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A B : VTy} {SM SD S : Row}
    {d : Expr} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B)
    (hS : SM.Unwind x) (hMS : RowLe SM S) (hDS : RowLe SD S)
    (hPend : SD.UnrD → SM.PendPers)
    (hd : SemJN (ℍ := ℍ) Δ Γ d (.val (.thunk (.arr (.mut a A) (CTy.effOf SD .unit))))) :
    SemJN (ℍ := ℍ) Δ Γ (withborUE d) (.val (withbor3UTyD a x Δ.meetOfDom A B SM S)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain rfl := gN_deadP hΓ hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ (withborUE d)) _
  rw [withborUE_psub γ d]
  refine erwp_val (v := withborUV (substAll γ d)) (withbor3UD_sem hδ hfree₁ hfree₂ hS hMS hDS hPend Θ n
    (fun Θ' hΘ' c' k hk ls' => ?_))
  have h := hd δ γ Θ' c' k ls' PMap.empty hδ hΘ' (consistentX_empty c') hlw
    (gN_dead_any hΓ hg Θ' k hk)
  exact h


/-- `withbor3UD_compatN` at `Σ_D = ∅`, `Σ_M = Σ`. -/
theorem withbor3U_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A B : VTy} {S : Row}
    {d : Expr} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B)
    (hS : S.Unwind x)
    (hd : SemJN (ℍ := ℍ) Δ Γ d (.val (.lolli (.mut a A) .unit))) :
    SemJN (ℍ := ℍ) Δ Γ (withborUE d) (.val (withbor3UTy a x Δ.meetOfDom A B S)) :=
  withbor3UD_compatN x hΓ hfree₁ hfree₂ hS (RowLe.refl S) (RowLe.nil S)
    (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) hd

/-! ### `withload` at an unwinding row -/

/-- **The unwinding callback at the image**: the callback, at `β ⊏ @bnd`, applied to the image
`χ` of the loaded payload, typed at `Imm̲ 'x A`, runs at the row's table with `[β]𝒱⟦B⟧` as its
post (`callback_at_image` at a `Row.Unwind` row, its table by `tabUN_extend`). -/
theorem callback_at_imageU {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy} {S : Row}
    (hB : ¬ VFree x B) (hS : S.Unwind x) {δ : LSub} {Θ : LocTy} (hΘ : Θ.OK)
    {c : Loc → Option Life} {n : Nat} {ls : List SRec} {f u : Val} {ρf χ Bχ : WRes} {β : Life}
    (hLt : LtLife δ bnd β)
    (hf : vN (ℍ := ℍ) (cbUTy x bnd (A.immReborrow (.var x)) B S) δ Θ n f ρf)
    (hcf : ConsistentX c ρf) (hχ : ∀ m (ψ : CellU Loc Val), χ.get m = some ψ → ψ.kind = Kind.imm)
    (himg : vN (ℍ := ℍ) (A.immReborrow (.var x)) (δ.extend x β) Θ n u χ)
    (hBχ : ResU.CompS ρf χ Bχ) :
    erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabUN (ℍ := ℍ) S δ Θ))
      (RebPost β (fun k _ v ρ => vN (ℍ := ℍ) B δ Θ k v ρ)) n ls
      (.app (.app (.val f) (.val .unit)) (.val u)) Bχ := by
  have h1 := (hf Θ (LocTy.extR_refl _ _) hΘ c hcf ls) β hLt
  have hcon : ConsistentX c Bχ := consistentX_compS hBχ hcf (consistentX_allImm hχ c)
  have h2 := h1 c n le_rfl u χ Bχ hBχ himg hcon
  rw [cN_unwind_iff hS, tabUN_extend hS δ Θ β] at h2
  refine erwp_mono (fun k _ w ρ hb => ?_) (opTableN_local _) n ls _ Bχ h2
  obtain ⟨α', hα', hbB, hst⟩ := hb
  rw [interp_ext_self] at hα'
  cases Option.some.inj hα'
  rw [vN_extend_of_not_free hB] at hbB
  exact ⟨hbB, hst⟩

/-- **`withload` at an unwinding row is a value of its type**: at
`Imm @a A ⊸ (∀'x ⊏ @Δ. Imm̲ 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ B` with `Σ` a `Row.Unwind x` row. Core's
`withloadU_compatX`, step by step, as `withloadS_compat`: the `Imm` argument is `loc ℓ`; the
load (`rwp_load_cell` under `erwp_bindR`); 6.150 at the run's first entry (`withload_rebT`),
across the row's raises (`erwp_rebGen`): the row's table admits the reborrow at every `β`
(`tabUN_rebOKR`; an unrestricted operation of the row is abortive, so it never resumes) and
has no cancel obligation (`tabUN_rebClosed`); the callback at the image
(`callback_at_imageU`), its result `['x] B` read at `B`. The source is consumed by the load, so
nothing goes back to the lender and there is no finaliser. -/
theorem withloadU_sem {Δ : LifeCtx} {a : Lifetime.Life} {x : LifeVar} {A B : VTy} {S : Row}
    {δ : LSub} (hδ : Δ.Models δ) (hA : ¬ VFree x A) (hB : ¬ VFree x B) (hS : S.Unwind x)
    (Θ₀ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (withloadUTy a x Δ.meetOfDom A B S) δ Θ₀ n withloadV PMap.empty := by
  intro Θ _ hΘ c₁ _ ls c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  intro c k' hk' f ρf ρ'' hc' hf hcon
  obtain ⟨α₀, hα₀, ⟨l, s, w, σ, hσs, rfl, rfl, hα₀s, hpay⟩, hwit⟩ :=
    vN_le hk' hu
  rw [cN_unwind_iff hS]
  refine erwp_of_valid fun hv'' => ?_
  have hcf : ConsistentX c ρf := consistentX_right hc' hcon hv''
  have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
  have hTd := opTableN_down (tabUN_down (ℍ := ℍ) S δ Θ)
  have hQo : PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) B δ Θ k v ρ) :=
    fun k _ v ρ h => vN_down _ δ Θ k v ρ h
  refine erwp_det hΦ hTd hQo
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl (.appL .hole f)) ?_
  refine erwp_det hΦ hTd hQo (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 f (Expr.subst (0 + 1) (Val.shift 1 0 (Val.loc l))
        (.app (.app v0 unit') (.app load' v1)))) =
      (Kont.appR (.app (.val f) (.val .unit)) .hole).plug
        (.app (.val (.prim .load)) (.val (Val.loc l))) := by
    simp [Kont.plug, Expr.subst, Expr.shift, Val.shift, Val.loc, Expr.val, Val.prim, v0, v1,
      unit', load', Val.unit]
  rw [e₃]
  -- the load
  refine erwp_bindR hΦ (opTableN_local _) _ ?_
  refine rwp_load_cell ls l s w σ hσs _ hc' ?_
  simp only [Kont.plug]
  -- 6.150 across the row's raises, the callback at the image
  exact withload_rebT (T := tabUN (ℍ := ℍ) S δ Θ) (Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries))
    hA (fun β _ => tabUN_rebOKR hS δ Θ β)
    (fun β _ _ _ _ _ _ χ Ok _ _ _ => tabUN_rebClosed hS δ Θ β _ χ Ok)
    (vO_le (Nat.sub_le k' 1) hpay) (hwit l s w σ hσs rfl)
    (fun β hLt u χ Bχ hχ _ _ himg hBχ =>
      callback_at_imageU hB hS hΘ hLt (vN_le (Nat.sub_le k' 1) hf) hcf hχ himg hBχ) hc'

/-- **`withloadU` at `SemJN`** (Core's `withloadU_compatX`), at an unwinding row and any `Δ`,
abortive unrestricted operations included. -/
theorem withloadU_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A B : VTy} {S : Row}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B)
    (hS : S.Unwind x) :
    SemJN (ℍ := ℍ) Δ Γ withload (.val (withloadUTy a x Δ.meetOfDom A B S)) := by
  intro δ γ Θ c n ls ρ hδ _ _ _ hg
  obtain rfl := gN_deadP hΓ hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ withload) _
  rw [show substAll γ withload = withload from psub_closedAt _ γ (by decide) (Nat.zero_le 0)]
  exact erwp_val (v := withloadV) (withloadU_sem hδ hfree₁ hfree₂ hS Θ n)

/-- **`withloadU` at the row with an unrestricted operation**, every hypothesis discharged. -/
theorem withloadU_unr_inst (Δ : LifeCtx) (a : Lifetime.Life) (x : LifeVar) :
    SemJN (ℍ := ℍ) Δ [] withload
      (.val (withloadUTy a x Δ.meetOfDom .unit .unit unrRaiseRow)) :=
  withloadU_compatN x .nil id id (unrRaiseRow_unwind x)

/-! ### The slice lends at an unwinding row -/

/-- **An unwinding row's table does not read a fresh key of the world**. -/
theorem tabUN_add {S : Row} {x : LifeVar} (hS : S.Unwind x) (δ : LSub) {Θ : LocTy} {α : Life}
    (hfr : Θ.Fresh α) (l : Loc) (F : Nat → Val → SPropS Loc Val α) :
    tabUN (ℍ := ℍ) S δ (Θ.add l α F) = tabUN (ℍ := ℍ) S δ Θ := by
  refine tabUN_congr fun o ho => ?_
  funext n v ρ
  have hρ := vN_unwind_inStratumK hS ho δ α
  exact propext ⟨fun h => vN_local _ δ Θ l α F n v ρ (hρ _ n v ρ h) h,
    fun h => vN_extA _ δ (LocTy.extA_add hfr l F) n v ρ h⟩

/-- **An unwinding row's table does not read an `imm` record of the world** -/
theorem tabUN_addImm {S : Row} {x : LifeVar} (hS : S.Unwind x) (δ : LSub) (Θ : LocTy)
    (y : SRec) : tabUN (ℍ := ℍ) S δ (Θ.addImm y) = tabUN (ℍ := ℍ) S δ Θ := by
  refine tabUN_congr fun o ho => ?_
  funext n v ρ
  have hρ := vN_unwind_inStratumK hS ho δ y.2
  exact propext ⟨fun h => vN_extR _ δ n v ρ (LocTy.extR_of_addImm Θ y.1 (hρ _ n v ρ h)) h,
    fun h => vN_extR _ δ n v ρ (LocTy.extR_addImm Θ y.1 (hρ _ n v ρ h)) h⟩

/-- `tabUN_addImm` at every list of records. -/
theorem tabUN_addImms {S : Row} {x : LifeVar} (hS : S.Unwind x) (δ : LSub) (Θ : LocTy) :
    ∀ xs : List SRec, tabUN (ℍ := ℍ) S δ (Θ.addImms xs) = tabUN (ℍ := ℍ) S δ Θ
  | [] => rfl
  | y :: xs => by
      rw [LocTy.addImms_cons, tabUN_addImm hS δ _ y, tabUN_addImms hS δ Θ xs]

/-- **One Mut Frame per place, around one expression, across raises** (Core's
`wpG_M_frameList`, the frames of `sliceBorrowMU_compatX` at an unwinding row): the list
induction over `erwp_M_frameRR`. The table `τ Θ c` does not read a fresh key (`hτ`), so every
frame's callback runs at the lender's table; frame `j`'s claim joins the inner frames' at a
raise, and the cells it claims are moved to the world without its key (`vN_local`), as in
`erwpK_M_frameListKWP`. -/
theorem erwp_M_frameListRN {A : VTy} {δ : LSub} {β β' : Life}
    (hunif : ∀ Θ j u r, vN (ℍ := ℍ) A δ Θ j u r → r.InStratum β)
    (τ : LocTy → (Loc → Option Life) → OpTabN)
    (hτ : ∀ (Θ : LocTy) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) c,
      Θ.Fresh α → τ (Θ.add l α F) (setLife c l α) = τ Θ c)
    (hτok : ∀ Θ c α, (τ Θ c).LendOKR α)
    (Ψ : LocTy → PostN) (hΨs : ∀ Θ k ls v ρ, Ψ Θ k ls v ρ → ρ.InStratum β')
    (hΨl : ∀ (Θ : LocTy) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) k ls v ρ,
      ρ.InStratum α → Ψ (Θ.add l α F) k ls v ρ → Ψ Θ k ls v ρ)
    (e : Expr) (ls : List SRec) :
    ∀ (I : List Loc) (Θ : LocTy) (c : Loc → Option Life) (n : Nat) (ρo ρH ρ : WRes) (γ : Life),
      Θ.OK → ConsistentX c ρ → ResU.CompS ρo ρH ρ →
      sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ n (Val.loc m)) I ρo →
      (∀ α, α < γ → ρH.InStratum α ∧ ∀ (Θ' : LocTy) (c' : Loc → Option Life), Θ.ExtA Θ' →
        Θ'.OK → ∀ ρm ρ', sepList (mutLeafN (ℍ := ℍ) A δ α Θ' n) I ρm → ResU.CompS ρH ρm ρ' →
          ConsistentX c' ρ' →
          erwp (ℍ := ℍ) (Θ'.view c') (opTableR (τ Θ' c') (claimL (ℍ := ℍ) A δ Θ' []))
            (Ψ Θ') n ls e ρ') →
      erwp (ℍ := ℍ) (Θ.view c) (opTableR (τ Θ c) (claimL (ℍ := ℍ) A δ Θ I))
        (fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
          sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ₁ ∧ Ψ Θ k ls' v ρ₂)
        n ls e ρ
  | [], Θ, c, n, ρo, ρH, ρ, γ, hΘ, hc, hcρ, ho, hH => by
      obtain ⟨rfl, -⟩ := ho
      rw [eq_of_compS_empty_left hcρ] at hc ⊢
      have h := (hH (↓γ) (Life.down_sqsubset γ)).2 Θ c (LocTy.extA_refl Θ) hΘ PMap.empty ρH
        ⟨rfl, trivial⟩ (ResU.comp_empty_right ρH) hc
      exact erwp_mono (fun k ls' v σ h' =>
        ⟨PMap.empty, σ, compS_empty_left σ, ⟨rfl, trivial⟩, h'⟩) (opTableR_local _ _) n ls e ρH h
  | ℓ :: I, Θ, c, n, ρo, ρH, ρ, γ, hΘ, hc, hcρ, ho, hH => by
      obtain ⟨ρ0, ρr, hc0, hleaf, hrest⟩ := ho
      obtain ⟨l, u, σ, hl, hcl, hu⟩ := hleaf
      obtain rfl : ℓ = l := loc_inj hl
      obtain ⟨Fr, hFr, hρ⟩ := compS_reassoc hc0 hcρ
      refine erwp_of_valid fun hv => ?_
      have hvρ0 : ResU.Valid ρ0 := (ResU.Valid.split hρ hv).1
      have hko : (CellU.ownOf (Loc := Loc) u).kind ≠ Kind.imm := by simp
      have hown : ρ0.get ℓ = some (CellU.ownOf u) :=
        (ResU.CompS.get_left_of_ne_imm hcl (ResU.single_get_self _ _) hko).2
      have hcF : ConsistentX c Fr := consistentX_right hρ hc hv
      have hcσ : ConsistentX c σ := consistentX_right hcl (consistentX_left hρ hc hv) hvρ0
      -- the outer frame's lifetime: fresh, below the frame's rest, `β` and `β′`
      obtain ⟨βF, hβF⟩ := ResU.exists_stratum Fr
      obtain ⟨α₁, hα₁le, hfr⟩ := LocTy.exists_fresh hΘ.2 (↓(βF ⊓ β ⊓ β'))
      have hα₁lt : α₁ < βF ⊓ β ⊓ β' := lt_of_le_of_lt hα₁le (Life.down_sqsubset _)
      have hα₁F : α₁ ≤ βF := hα₁lt.le.trans (inf_le_left.trans inf_le_left)
      have hα₁β : α₁ ≤ β := hα₁lt.le.trans (inf_le_left.trans inf_le_right)
      have hα₁β' : α₁ ≤ β' := hα₁lt.le.trans inf_le_right
      set P : CPredL := fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r with hP
      set Fm : Nat → Val → SPropS Loc Val α₁ := famL α₁ P Θ with hFm
      have hFmD : DownFam α₁ Fm := vN_fam_down A δ α₁ Θ
      have houtP : σ.InStratum α₁ := (hunif Θ n u σ hu).mono hα₁β
      have houtb : Fr.InStratum (↓α₁) := hβF.mono ((Life.down_sqsubset α₁).le.trans hα₁F)
      have hwit : Fm n u ⟨σ, houtP⟩ := (vN_above A δ Θ houtP).mpr hu
      set Θ₁ := Θ.add ℓ α₁ Fm with hΘ₁
      set c₁ := setLife c ℓ α₁ with hc₁
      have hOK₁ : Θ₁.OK := by
        obtain ⟨N, hN⟩ := hΘ.2
        exact ⟨LocTy.down_add hΘ.1 ℓ hFmD, ⟨min N (↓α₁), LocTy.fresh_add hN (min_le_left _ _)
          (lt_of_le_of_lt (min_le_right _ _) (Life.down_sqsubset α₁)) ℓ Fm⟩⟩
      have hE₁ : Θ.ExtA Θ₁ := LocTy.extA_add hfr ℓ Fm
      have hview : Θ₁.view c₁ = (Θ.view c).set ℓ α₁ Fm := LocTy.view_add Θ c ℓ α₁ Fm
      have hcF₁ : ConsistentX c₁ Fr :=
        consistentX_setLife hcF (exS_none_of_part hρ hv hown hko) α₁
      have hcσ₁ : ConsistentX c₁ σ :=
        consistentX_setLife hcσ (exS_none_of_part hcl hvρ0 (ResU.single_get_self _ _) hko) α₁
      have hRs : ∀ k ρ', claimL (ℍ := ℍ) A δ Θ₁ I k ρ' → ρ'.InStratum α₁ := fun k ρ' h =>
        sepList_closed (ResU.inStratum_empty α₁) (fun _ _ _ hc a b => inStratum_compS hc a b)
          (fun m τ hm => ownLeafN_inStratum hα₁β hunif hm) h
      have hcl' : ∀ k ρ', (claimR ℓ α₁ Fm k ⋆ claimL (ℍ := ℍ) A δ Θ₁ I k) ρ' →
          claimL (ℍ := ℍ) A δ Θ (ℓ :: I) k ρ' := by
        rintro k ρ' ⟨ρ₁, ρ₂, hc12, ⟨w, σ', hσ', hFσ, hcw⟩, hr⟩
        refine ⟨ρ₁, ρ₂, hc12, ⟨ℓ, w, σ', rfl, hcw, (vN_above A δ Θ hσ').mp hFσ⟩, ?_⟩
        exact sepList_mono_down (R := fun τ => τ.InStratum α₁)
          (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
            ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
          (fun m τ hτ hm => vN_local (.ref A) δ Θ ℓ α₁ Fm k _ τ hτ hm) (hRs k ρ₂ hr) hr
      have hM := erwp_M_frameRR (Φ := Θ.view c) (l := ℓ) (A := α₁) (F := Fm) hFmD
        (hτok Θ c α₁) hRs
        (Q := fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
          sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) (ℓ :: I) ρ₁ ∧ Ψ Θ k ls' v ρ₂)
        n n le_rfl ls e u σ ρ0 Fr ρ houtP houtb (Fm n) (fun _ _ h => h) hwit hcl hρ
        (fun BM hBM => ?_)
      · exact erwp_opTableR_le (OpTabN.Sub.le fun _ _ _ h => h) hcl' n ls e ρ hM
      rw [← hview, ← hτ Θ ℓ α₁ Fm c hfr]
      obtain ⟨R, hR, hBMR⟩ := compS_reassoc hFr hBM
      have hcBM : ConsistentX c₁ BM := consistentX_compS hBM hcF₁
        (consistentX_single_mut hcσ₁ (by simp [hc₁, setLife]))
      obtain ⟨βR, hβR⟩ := ResU.exists_stratum R
      have hrest₁ : sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ₁ n (Val.loc m)) I ρr :=
        sepList_mono' (fun m τ h => vN_extA (.ref A) δ hE₁ n _ τ h) hrest
      refine erwp_mono (fun k ls' v ρ' h => ?_) (opTableR_local _ _) n ls e BM
        (erwp_M_frameListRN hunif τ hτ hτok Ψ hΨs hΨl e ls I Θ₁ c₁ n ρr R BM (βR ⊓ α₁ ⊓ γ) hOK₁
          hcBM hBMR hrest₁ (fun α₂ hα₂ => ⟨hβR.mono (le_of_lt (lt_of_lt_of_le hα₂
            (inf_le_left.trans inf_le_left))), ?_⟩))
      · obtain ⟨ρ₁, ρ₂, hc12, ho1, hψ⟩ := h
        have hs1 : ρ₁.InStratum α₁ := sepList_closed (ResU.inStratum_empty α₁)
          (fun _ _ _ hc a b => inStratum_compS hc a b)
          (fun m τ hm => ownLeafN_inStratum hα₁β hunif hm) ho1
        have hs2 : ρ₂.InStratum α₁ := (hΨs _ _ _ _ _ hψ).mono hα₁β'
        refine ⟨inStratum_compS hc12 hs1 hs2, fun w Y hY σ' ⟨hσ', hFσ⟩ Z hZ => ?_⟩
        have ho1' : sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ₁ :=
          sepList_mono_down (R := fun τ => τ.InStratum α₁)
            (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
              ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
            (fun m τ hτ hm => vN_local (.ref A) δ Θ ℓ α₁ Fm k _ τ hτ hm) hs1 ho1
        have hψ' := hΨl Θ ℓ α₁ Fm k ls' v ρ₂ hs2 hψ
        have hwA : vN (ℍ := ℍ) A δ Θ k w σ' := (vN_above A δ Θ hσ').mp hFσ
        obtain ⟨cp, hcp, hZ'⟩ := compS_reassoc hY hZ
        obtain ⟨oc, hoc, hZ''⟩ := compS_exch hc12 hZ'
        exact ⟨oc, ρ₂, hZ'', ⟨cp, ρ₁, ResU.CompS.comm hoc, ⟨ℓ, w, σ', rfl, hcp, hwA⟩, ho1'⟩, hψ'⟩
      · intro Θ' c' hE hOK' ρm₂ ρ' hm₂ hcomp hc'
        have hα₂γ : α₂ < γ := lt_of_lt_of_le hα₂ inf_le_right
        have hα₂α₁ : α₂ ≤ α₁ := le_of_lt (lt_of_lt_of_le hα₂ (inf_le_left.trans inf_le_right))
        obtain ⟨X, hX, hρ'X⟩ := compS_reassoc hR hcomp
        have hlead : mutLeafN (ℍ := ℍ) A δ α₂ Θ' n ℓ
            (ResU.single ℓ (CellU.mutOf α₁ u σ houtP (Fm n) hwit)) :=
          ⟨α₁, hα₂α₁, mutL_extR (hE.extR _) (lend_mutL Θ ℓ α₁ P le_rfl houtP hwit),
            fun Θ'' j w r h => (hunif Θ'' j w r h).mono hα₁β⟩
        exact (hH α₂ hα₂γ).2 Θ' c' (LocTy.extA_trans hE₁ hE) hOK' X ρ' ⟨_, ρm₂, hX, hlead, hm₂⟩
          hρ'X hc'

/-- **The finaliser consumes the source array, its judgment read at the index** (`fin_claimI`
at `Array A`). -/
theorem fin_claimArrI {A : VTy} {d : Expr} {δ : LSub} {Θ : LocTy}
    (hΘ : Θ.OK) {c : Loc → Option Life} {N : Nat}
    (hd : ∀ k, k ≤ N → ∀ ls, cN (ℍ := ℍ) (.ret (.lolli (.array A) .unit)) δ Θ c k ls d PMap.empty)
    {a : Val} {k : Nat} (hk : k ≤ N) {ls : List SRec} {ρ : WRes}
    (h : vN (ℍ := ℍ) (.array A) δ Θ k a ρ) (hc : ConsistentX c ρ) :
    rwp (ℍ := ℍ) (Θ.view c) (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
      (.app (.val (DFa (d.shift 1 0) a)) (.val .unit)) ρ := by
  have hΦ := LocTy.view_down hΘ.1 c
  obtain ⟨l, cn, rfl, -, -⟩ := id h
  refine Hardest791.rwp_det'' (Q := fun _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) hΦ
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (.app (d.shift 1 0) (.val (Val.arr l cn)))) =
      (Kont.appL .hole (Val.arr l cn)).plug d := by
    simp [Kont.plug, Expr.subst, subst_shift_succ (j := 0) (d := 0) _ d (le_refl _), Expr.shift_zero, subst_arr]
  rw [e]
  refine rwp_bind hΦ _ ?_
  have hd0 := hd k hk ls
  have hfr := rwp_frame (fun _ τ => τ = ρ) (fun _ _ _ _ h => h) (compS_empty_left ρ)
    (rwp_of_erwp_empty (erwp_of_cN_ret hd0)) rfl
  refine rwp_mono_le (fun k' hk' ls' v τ hv => ?_) (rwp_consistentXV hfr hc)
  obtain ⟨⟨τ₁, τ₂, hcτ, hP, rfl⟩, hcτ', hvτ⟩ := hv
  have := hP Θ (LocTy.extR_refl Θ _) hΘ c (consistentX_left hcτ hcτ' hvτ) ls'
    c k' le_rfl (Val.arr l cn) τ₂ τ hcτ (vN_le hk' h) hcτ'
  exact rwp_of_erwp_empty (erwp_of_cN_ret this)

/-- **`slice_borrow_mut` at an unwinding row is a value of its type** (Core's
`sliceBorrowMU_compatX`): `withborU d` at
`Array A ⊸ (∀'x ⊏ @Δ. [Mut 'x A] ⊸ F_Σ(['x] B)) ⊸ F_Σ(Array A ⊗ B)`, `Σ` a `Row.Unwind x`
row. `withbor2U_sem`'s steps with the one-cell frame replaced by the `n`-cell frame across the
row's raises (`erwp_M_frameListRN`, Core's `wpG_M_frameFam`), the row's table reading no fresh
key (`tabUN_add`); the payloads' and the result's strata from the side conditions by 6.60
at `↓@bδ`; the callback receives the family `[Mut 'x A]` at the innermost lifetime; the
composite claim, the array owned again, consistent with the view (`erwp_claimX_abort`), is
consumed by the finaliser at a raise (`erwp_ubindRaise`, `fin_claimArrI`). -/
theorem sliceBorrowMU_sem {Δ : LifeCtx} {x : LifeVar} {A B : VTy} {S : Row} {d : Expr}
    {δ : LSub} (hδ : Δ.Models δ) (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) (hA : ¬ VFree x A) (hB : ¬ VFree x B)
    (hS : S.Unwind x) (Θ₀ : LocTy) (n : Nat)
    (hd : ∀ (Θ : LocTy), Θ.OK → ∀ c k, k ≤ n → ∀ ls,
      cN (ℍ := ℍ) (.ret (.lolli (.array A) .unit)) δ Θ c k ls d PMap.empty) :
    vN (ℍ := ℍ) (sliceBorrowMUTy x Δ.meetOfDom A B S) δ Θ₀ n (withborUV d) PMap.empty := by
  intro Θ _ hΘ c₁ _ ls c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  intro c k' hk' f ρf ρ'' hc' hf hcon
  obtain ⟨l, cn, rfl, hn, hs⟩ := vN_le hk' hu
  rw [cN_unwind_iff hS]
  refine erwp_of_valid fun hv'' => ?_
  have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
  set Fo := CTy.effOf S (.tensor (.array A) B) with hFo
  set T := tabUN (ℍ := ℍ) S δ Θ with hTdef
  have hTd : T.Down := tabUN_down S δ Θ
  have hQo : PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) (.tensor (.array A) B) δ Θ k v ρ) :=
    fun k _ v ρ h => vN_down _ δ Θ k v ρ h
  refine erwp_det hΦ (opTableN_down hTd) hQo
    (fun μ => step1Only_plug (Head.beta μ _ (Val.arr l cn)) rfl (.appL .hole f)) ?_
  refine erwp_det hΦ (opTableN_down hTd) hQo (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 f (Expr.subst (0 + 1) (Val.shift 1 0 (Val.arr l cn))
        (thenE ((Expr.var 2).pair (Expr.var 0)) ((d.shift 3 0).app (Expr.var 2))
          (((Expr.var 0).app (Expr.val Val.unit)).app (Expr.var 1))))) =
      ubindE (.pair (NFa (Val.arr l cn)) (DFa (d.shift 1 0) (Val.arr l cn)))
        (.app (.app (.val f) (.val .unit)) (.val (Val.arr l cn))) := by
    simp [Kont.plug, Expr.subst, thenE, ubindE, NFa, DFa, Val.pair,
      Val.lam, Expr.val, Val.prim, shift_arr, subst_arr,
      subst_shift_succ (j := 2) (d := 2) _ d (le_refl _),
      subst_shift_succ (j := 1) (d := 1) _ d (le_refl _)]
  rw [e₃]
  obtain ⟨a, hdefa, hOa⟩ := hsideA
  obtain ⟨βP, hβP⟩ := hdefa δ hδ
  have hunif : ∀ Θ j w r, vN (ℍ := ℍ) A δ Θ j w r → r.InStratum (↓βP) :=
    vN_outlivesLe hδ hβP (Life.down_sqsubset βP) hOa
  obtain ⟨b, hdefb, hOb⟩ := hsideB
  obtain ⟨βB, hβB⟩ := hdefb δ hδ
  have hBs : ∀ Θ j w r, vN (ℍ := ℍ) B δ Θ j w r → r.InStratum (↓βB) :=
    vN_outlivesLe hδ hβB (Life.down_sqsubset βB) hOb
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  have hBδ : ∀ α, vN (ℍ := ℍ) B (δ.extend x α) = vN (ℍ := ℍ) B δ :=
    fun α => vN_extend_of_not_free hB δ α
  set I := rangeLocs l cn.toNat with hI
  let Ψ : LocTy → PostN := fun Θ k _ v ρ => vN (ℍ := ℍ) B δ Θ k v ρ
  have hM := erwp_M_frameListRN hunif (fun Θ _ => tabUN (ℍ := ℍ) S δ Θ)
    (fun Θ l₀ α F c₀ hf₀ => tabUN_add hS δ hf₀ l₀ F)
    (fun Θ c₀ α => tabUN_lendOKR hS δ Θ α) Ψ
    (fun Θ k _ v ρ hw => hBs Θ k v ρ hw)
    (fun Θ l₀ α F k _ v ρ hρ hw => vN_local B δ Θ l₀ α F k v ρ hρ hw)
    (.app (.app (.val f) (.val .unit)) (.val (Val.arr l cn))) ls I Θ c k' ρu ρf ρ'' (m ⊓ βf)
    hΘ hcon hc' (by rw [← sepRange_eq_sepList]; exact hs)
    (fun α hα => ⟨hβf.mono (le_of_lt (lt_of_lt_of_le hα inf_le_right)), ?_⟩)
  · have hM' := erwp_claimX_abort (tabUN_abort hS δ Θ) hcon hM
    have hM'' := erwp_mono_le
      (Tb' := opTableR T (fun j ρ => claimX (claimL (ℍ := ℍ) A δ Θ I) c j ρ ∧ j ≤ k')) k'
      (fun _ _ _ _ _ h => h) (fun j hj ls' t Ψ Ψ' ρ hΨ h => by
        rcases h with ⟨K, m, i, v, en, h⟩ | ⟨K, m, i, v, en, h⟩
        · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp h
          exact absurd ha (by rw [tabUN_abort hS δ Θ m i en hTe]; decide)
        · obtain ⟨hp, τ, τR, hcτ, h₁, hR⟩ := pure_sep_iff.mp h
          exact Or.inr ⟨K, m, i, v, en, pure_sep_mk hp ⟨τ, τR, hcτ, h₁, hR, hj⟩⟩)
      k' le_rfl ls _ ρ'' hM'
    refine erwp_ubindRaise hΦ hTd
      (fun m i en h ha => by rw [tabUN_abort hS δ Θ m i en h] at ha; cases ha)
      (tabUN_named hS δ Θ)
      (fun m i en h k ls ls' v ρ _ hp => by
        obtain ⟨o, ho, -, rfl⟩ := tabUN_some h
        exact hp)
      (NFa (Val.arr l cn)) (DFa (d.shift 1 0) (Val.arr l cn)) (fun j ls' ρ hR => ?_) hQo
      (fun j ls' b ρ hq => ?_) k' ls _ ρ'' hM''
    · obtain ⟨⟨hR, hcR⟩, hj⟩ := hR
      exact fin_claimArrI hΘ (fun j' hj' ls => hd Θ hΘ c j' (hj'.trans (hk'.trans hk)) ls)
        (hj.trans le_rfl) ⟨l, cn, rfl, hn, by rw [sepRange_eq_sepList]; exact hR⟩ hcR
    · obtain ⟨ρ₁, ρ₂, hc12, ho, hb⟩ := hq
      refine erwp_det hΦ (opTableN_down hTd) hQo
        (fun μ => step1Only_plug (Head.beta μ _ b) rfl .hole) ?_
      simp [Kont.plug, Expr.subst]
      exact erwp_val (v := Val.pair (Val.arr l cn) b)
        ⟨Val.arr l cn, b, ρ₁, ρ₂, rfl, hc12,
          ⟨l, cn, rfl, hn, by rw [sepRange_eq_sepList]; exact ho⟩, hb⟩
  -- the callback, at the frames' world and view, from the leaves at `α`
  intro Θ'' c'' hE hOK'' ρm ρ₃ hml hcomp hc''
  refine erwp_of_valid fun hv₃ => ?_
  have hLt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_left⟩
  have hcf : ConsistentX c'' ρf := consistentX_left hcomp hc'' hv₃
  have hfam : vN (ℍ := ℍ) (.sliceMut (.var x) A) (δ.extend x α) Θ'' k' (Val.arr l cn) ρm :=
    ⟨l, cn, rfl, hn, by
      rw [sepRange_eq_sepList]; exact sepList_mono' (fun _ _ h => vN_mutLeaf hA h) hml⟩
  have h1 := (hf Θ'' (hE.extR ρf) hOK'' c'' hcf ls) α hLt
  have h2 := h1 c'' k' le_rfl (Val.arr l cn) _ ρ₃ hcomp hfam hc''
  rw [cN_unwind_iff hS, tabUN_extend hS δ Θ'' α] at h2
  refine erwp_opTableN_R (OpTabN.Sub.le fun _ _ _ h => h) (R₀ := claimL (ℍ := ℍ) A δ Θ'' [])
    (fun _ => ⟨rfl, trivial⟩) k' ls _ ρ₃
    (erwp_mono (fun k ls' b ρ' hb => ?_) (opTableN_local _) k' ls _ ρ₃ h2)
  obtain ⟨β, hβ, hbB, -⟩ := hb
  rw [interp_ext_self] at hβ
  cases Option.some.inj hβ
  show vN (ℍ := ℍ) B δ Θ'' k b ρ'
  rw [← hBδ α]; exact hbB

/-- **`sliceBorrowMU` at `SemJN`** (Core's `sliceBorrowMU_compatX`), at an unwinding row and any
`Δ`. -/
theorem sliceBorrowMU_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} {S : Row} {d : Expr}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) (hfree₁ : ¬ VFree x A)
    (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
    (hd : SemJN (ℍ := ℍ) Δ Γ d (.val (.lolli (.array A) .unit))) :
    SemJN (ℍ := ℍ) Δ Γ (withborUE d) (.val (sliceBorrowMUTy x Δ.meetOfDom A B S)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain rfl := gN_deadP hΓ hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ (withborUE d)) _
  rw [withborUE_psub γ d]
  refine erwp_val (v := withborUV (substAll γ d)) (sliceBorrowMU_sem hδ hsideA hsideB hfree₁ hfree₂ hS Θ n
    (fun Θ' hΘ' c' k hk ls' => ?_))
  have h := hd δ γ Θ' c' k ls' PMap.empty hδ hΘ' (consistentX_empty c') hlw
    (gN_dead_any hΓ hg Θ' k hk)
  exact h

/-- **`slice_borrow` at an unwinding row is a value of its type** (Core's
`sliceBorrowIU_compatX`): `withborU d` at
`Array A ⊸ (∀'x ⊏ @Δ. [Imm 'x A] ⊸ F_Σ(['x] B)) ⊸ F_Σ(Array A ⊗ B)`, `Σ` a `Row.Unwind x` row.
`sliceBorrowMU_sem`'s steps with the `n` Imm Frames across the row's raises
(`erwp_I_frameListRN`, Core's `wpG_I_frameFam`) at the lender's table, which reads no record
(`tabUN_addImms`); the payloads' and the result's strata from the side conditions by 6.60
at `↓@bδ`; the callback at the world holding the records receives the family `[Imm 'x A]` at the
innermost lifetime; the composite claim, the array owned again, consistent with the view
(`erwp_claimX_abort`), is consumed by the finaliser at a raise (`erwp_ubindRaise`,
`fin_claimArrI`). -/
theorem sliceBorrowIU_sem {Δ : LifeCtx} {x : LifeVar} {A B : VTy} {S : Row} {d : Expr}
    {δ : LSub} (hδ : Δ.Models δ) (hadm : AdmWf A δ)
    (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) (hA : ¬ VFree x A) (hB : ¬ VFree x B)
    (hS : S.Unwind x) (Θ₀ : LocTy) (n : Nat)
    (hd : ∀ (Θ : LocTy), Θ.OK → ∀ c k, k ≤ n → ∀ ls,
      cN (ℍ := ℍ) (.ret (.lolli (.array A) .unit)) δ Θ c k ls d PMap.empty) :
    vN (ℍ := ℍ) (sliceBorrowIUTy x Δ.meetOfDom A B S) δ Θ₀ n (withborUV d) PMap.empty := by
  intro Θ _ hΘ c₁ _ ls c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  intro c k' hk' f ρf ρ'' hc' hf hcon
  obtain ⟨l, cn, rfl, hn, hs⟩ := vN_le hk' hu
  rw [cN_unwind_iff hS]
  refine erwp_of_valid fun hv'' => ?_
  have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
  set Fo := CTy.effOf S (.tensor (.array A) B) with hFo
  set T := tabUN (ℍ := ℍ) S δ Θ with hTdef
  have hTd : T.Down := tabUN_down S δ Θ
  have hQo : PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) (.tensor (.array A) B) δ Θ k v ρ) :=
    fun k _ v ρ h => vN_down _ δ Θ k v ρ h
  refine erwp_det hΦ (opTableN_down hTd) hQo
    (fun μ => step1Only_plug (Head.beta μ _ (Val.arr l cn)) rfl (.appL .hole f)) ?_
  refine erwp_det hΦ (opTableN_down hTd) hQo (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 f (Expr.subst (0 + 1) (Val.shift 1 0 (Val.arr l cn))
        (thenE ((Expr.var 2).pair (Expr.var 0)) ((d.shift 3 0).app (Expr.var 2))
          (((Expr.var 0).app (Expr.val Val.unit)).app (Expr.var 1))))) =
      ubindE (.pair (NFa (Val.arr l cn)) (DFa (d.shift 1 0) (Val.arr l cn)))
        (.app (.app (.val f) (.val .unit)) (.val (Val.arr l cn))) := by
    simp [Kont.plug, Expr.subst, thenE, ubindE, NFa, DFa, Val.pair,
      Val.lam, Expr.val, Val.prim, shift_arr, subst_arr,
      subst_shift_succ (j := 2) (d := 2) _ d (le_refl _),
      subst_shift_succ (j := 1) (d := 1) _ d (le_refl _)]
  rw [e₃]
  have hcf : ConsistentX c ρf := consistentX_right hc' hcon hv''
  obtain ⟨a, hdefa, hOa⟩ := hsideA
  obtain ⟨βP, hβP⟩ := hdefa δ hδ
  have hunif : ∀ Θ j w r, vN (ℍ := ℍ) A δ Θ j w r → r.InStratum (↓βP) :=
    vN_outlivesLe hδ hβP (Life.down_sqsubset βP) hOa
  obtain ⟨b, hdefb, hOb⟩ := hsideB
  obtain ⟨βB, hβB⟩ := hdefb δ hδ
  have hBs : ∀ Θ j w r, vN (ℍ := ℍ) B δ Θ j w r → r.InStratum (↓βB) :=
    vN_outlivesLe hδ hβB (Life.down_sqsubset βB) hOb
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  have hBδ : ∀ α, vN (ℍ := ℍ) B (δ.extend x α) = vN (ℍ := ℍ) B δ :=
    fun α => vN_extend_of_not_free hB δ α
  set I := rangeLocs l cn.toNat with hI
  let Ψ : LocTy → PostN := fun Θ k _ v ρ => vN (ℍ := ℍ) B δ Θ k v ρ
  have hab := tabUN_abort (ℍ := ℍ) hS δ Θ
  have hM := erwp_I_frameListRN hadm hunif T hab
    (fun α => tabUN_iLendOKR hS δ Θ α) Ψ
    (fun Θ k _ v ρ hw => hBs Θ k v ρ hw)
    (fun Θ r α k _ v ρ hρ hw => vN_extR B δ k v ρ (LocTy.extR_of_addImm Θ r hρ) hw)
    (fun _ _ _ _ _ _ h => h) (.app (.app (.val f) (.val .unit)) (.val (Val.arr l cn))) c
    I Θ k' ls ρu ρf ρ'' (m ⊓ βf) hcf hc' (by rw [← sepRange_eq_sepList]; exact hs)
    (fun α hα => ⟨hβf.mono (le_of_lt (lt_of_lt_of_le hα inf_le_right)), ?_⟩)
  · have hM' := erwp_claimX_abort hab hcon hM
    have hM'' := erwp_mono_le
      (Tb' := opTableR T (fun j ρ => claimX (fun _ => claimL (ℍ := ℍ) A δ Θ I k') c j ρ ∧
        j ≤ k')) k'
      (fun _ _ _ _ _ h => h) (fun j hj ls' t Ψ Ψ' ρ hΨ h => by
        rcases h with ⟨K, m, i, v, en, h⟩ | ⟨K, m, i, v, en, h⟩
        · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp h
          exact absurd ha (by rw [hab m i en hTe]; decide)
        · obtain ⟨hp, τ, τR, hcτ, h₁, hR⟩ := pure_sep_iff.mp h
          exact Or.inr ⟨K, m, i, v, en, pure_sep_mk hp ⟨τ, τR, hcτ, h₁, hR, hj⟩⟩)
      k' le_rfl ls _ ρ'' hM'
    refine erwp_ubindRaise hΦ hTd
      (fun m i en h ha => by rw [hab m i en h] at ha; cases ha)
      (tabUN_named hS δ Θ)
      (fun m i en h k ls ls' v ρ _ hp => by
        obtain ⟨o, ho, -, rfl⟩ := tabUN_some h
        exact hp)
      (NFa (Val.arr l cn)) (DFa (d.shift 1 0) (Val.arr l cn)) (fun j ls' ρ hR => ?_) hQo
      (fun j ls' b ρ hq => ?_) k' ls _ ρ'' hM''
    · obtain ⟨⟨hR, hcR⟩, hj⟩ := hR
      exact fin_claimArrI hΘ (fun j' hj' ls => hd Θ hΘ c j' (hj'.trans (hk'.trans hk)) ls)
        (hj.trans le_rfl) (vN_le hj ⟨l, cn, rfl, hn, by rw [sepRange_eq_sepList]; exact hR⟩) hcR
    · obtain ⟨ρ₁, ρ₂, hc12, ho, hb⟩ := hq
      refine erwp_det hΦ (opTableN_down hTd) hQo
        (fun μ => step1Only_plug (Head.beta μ _ b) rfl .hole) ?_
      simp [Kont.plug, Expr.subst]
      exact erwp_val (v := Val.pair (Val.arr l cn) b)
        ⟨Val.arr l cn, b, ρ₁, ρ₂, rfl, hc12,
          ⟨l, cn, rfl, hn, by rw [sepRange_eq_sepList]; exact ho⟩, hb⟩
  -- the callback, at the world holding the records, from the leaves at `α`
  intro xs ls₂ hxs _ ρm ρ₃ hml hcomp hc''
  set W := Θ.addImms xs with hW
  have hOKW : W.OK := LocTy.addImms_ok hΘ xs
  have hEW : Θ.ExtR W ρf := LocTy.extR_addImms Θ xs fun x hx =>
    hβf.mono (le_of_lt (lt_of_lt_of_le (hxs x hx).1 inf_le_right))
  have hLt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_left⟩
  have hfam : vN (ℍ := ℍ) (.arrayImm (.var x) A) (δ.extend x α) W k' (Val.arr l cn) ρm :=
    ⟨l, cn, rfl, hn, by
      rw [sepRange_eq_sepList]; exact sepList_mono' (fun _ _ h => vN_immLeaf hA h) hml⟩
  have h1 := (hf W hEW hOKW c hcf ls₂) α hLt
  have h2 := h1 c k' le_rfl (Val.arr l cn) _ ρ₃ hcomp hfam hc''
  rw [cN_unwind_iff hS, tabUN_extend hS δ W α, hW, tabUN_addImms hS δ Θ xs] at h2
  refine erwp_opTableN_R (OpTabN.Sub.le fun _ _ _ h => h)
    (R₀ := fun _ => claimL (ℍ := ℍ) A δ Θ [] k') (fun _ => ⟨rfl, trivial⟩) k' ls₂ _ ρ₃
    (erwp_mono (fun k ls' b ρ' hb => ?_) (opTableN_local _) k' ls₂ _ ρ₃ h2)
  obtain ⟨β, hβ, hbB, -⟩ := hb
  rw [interp_ext_self] at hβ
  cases Option.some.inj hβ
  show vN (ℍ := ℍ) B δ (Θ.addImms xs) k b ρ'
  rw [← hBδ α]; exact hbB

/-- **`sliceBorrowIU` at `SemJN`** (Core's `sliceBorrowIU_compatX`), at an unwinding row and any
`Δ`. -/
theorem sliceBorrowIU_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} {S : Row} {d : Expr}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hsc : VScoped Δ A)
    (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) (hfree₁ : ¬ VFree x A)
    (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
    (hd : SemJN (ℍ := ℍ) Δ Γ d (.val (.lolli (.array A) .unit))) :
    SemJN (ℍ := ℍ) Δ Γ (withborUE d) (.val (sliceBorrowIUTy x Δ.meetOfDom A B S)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain rfl := gN_deadP hΓ hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ (withborUE d)) _
  rw [withborUE_psub γ d]
  refine erwp_val (v := withborUV (substAll γ d)) (sliceBorrowIU_sem hδ (admWf_of_vScoped hsc hδ) hsideA hsideB
    hfree₁ hfree₂ hS Θ n (fun Θ' hΘ' c' k hk ls' => ?_))
  have h := hd δ γ Θ' c' k ls' PMap.empty hδ hΘ' (consistentX_empty c') hlw
    (gN_dead_any hΓ hg Θ' k hk)
  exact h

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
