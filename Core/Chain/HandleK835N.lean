import Core.Chain.MechK835N4
import Core.Chain.TabK835N

/-!
# A handler at `erwpK`: `[handle]` across Kripke stops  `[spec §19, §27, §62]`

`docs/new-core/scope-835-kripke-stop.md` §2, class M (handlers), and `scope-835-restriction.md`
§5. `erwp_handle_le` (`SI/HandleN.lean`) restated over a world index: the same induction on the
index and `ewp_handle_or`'s case split at the end of the handled run.

* **`[ret]`.** The handled run's value is posted at a world `y` the post order allows; the return
  clause runs there and is read back at the run's world along the post order (`erwpK_shift`).
* **`[op]` at the handler's name.** The clause receives the stopped run's Kripke stop
  (`KapRelK`): the floor the stop chose, and at every world the entry allows there, the resumed
  run and the cancel run, both read at that world. The clause does not know the floor; it is the
  one the stop chose. For a must-resume or cancellable entry `κ` owns its capture cell, so the
  entry's order at `κ`'s share is read at the part the stop left (`hwk`); `κ`'s share is part of
  the resource after the cell's allocation, which is valid (`erwpK_allocV`).
* **An operation of another name** passes outward at the same entry (`hTin`) and the same floor,
  its continuation re-entered under the handler at the resumption world.
* **Abortive stops** read no world.

Each `erwp` statement is proved again at one world (`*_of_K`); its text is the original's.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload hndE kappa kappaC
  kappaCell kappaAt capTag clauseAt hndVal ccatchE)

variable {ι : Type}

/-- `OpTabK.Down`'s cancel obligations, down any distance, at every world. -/
theorem OpTabK.Down.fin_le {T : OpTabK ι} (hT : T.Down) {n i : UInt32} {en : OpEntK ι}
    (hn : T n i = some en) {P : ι → Nat → List SRec → Expr → WProp} (hP : en.fin = some P)
    {y : ι} {m k : Nat} (h : m ≤ k) {ls : List SRec} {e : Expr} {ρ : WRes} (hk : P y k ls e ρ) :
    P y m ls e ρ := by
  induction h with
  | refl => exact hk
  | step _ ih => exact ih (hT.fin _ _ _ _ hn hP _ _ _ _ _ hk)

/-! ### `κ` -/

/-- Resuming `κ` at `w` runs `hnd H K[w]`, at `erwpK` (`erwp_kappa_resume`). -/
theorem erwpK_kappa_resume {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι}
    {Q : ι → PostN} {x : ι} (hΦ : (Φ x).Down) (hTd : (Tb x).Down) (hQ : ∀ y, (Q y).Down)
    (H : Val) (K : Kont) (w : Val) {k : Nat} {ls : List SRec} {ρ : WRes}
    (h : erwpK (ℍ := ℍ) V Φ Tb Q x k ls (hndE H (K.plug (.val w))) ρ) :
    erwpK (ℍ := ℍ) V Φ Tb Q x k ls (.app (.app (kappa H K) (.val (Val.inj₁ .unit))) (.val w))
      ρ := by
  refine erwpK_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.beta μ _ _) rfl (Kont.appL .hole w)) ?_
  refine erwpK_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl (Kont.appL .hole w)) ?_
  refine erwpK_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.seq μ _) rfl (Kont.appL .hole w)) ?_
  refine erwpK_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 1 + 1 : Nat) = 2 from rfl, kappa_resume_subst]
  exact h

/-- **An allocation at an evaluation position, in front of an `erwpK`**, the resource after it
valid (`erwp_alloc`, with `rwpG_validK` at the step's returned resource). -/
theorem erwpK_allocV {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι}
    (hL : ∀ x, (Tb x).Local) {Q : ι → PostN} {x : ι} (hΦ : (Φ x).Down) (Kc : Kont) (v : Val)
    {n : Nat} {ls : List SRec} {ρ : WRes}
    (h : ∀ (ℓ : Loc) (σ₁ σ₂ : WRes), ptoOwn ℓ v σ₁ → ResU.CompS ρ σ₁ σ₂ → ResU.Valid σ₂ →
      erwpK (ℍ := ℍ) V Φ Tb Q x (n - 1) ls (Kc.plug (.val (Val.loc ℓ))) σ₂) :
    erwpK (ℍ := ℍ) V Φ Tb Q x n ls (Kc.plug (.app (.val (.prim .alloc)) (.val v))) ρ := by
  rw [erwpK_eq]
  refine rwpG_bind hΦ Kc ?_
  have ha := rwp_alloc (ℍ := ℍ) (Φ := Φ x) ls v
    (fun k ls' w ρ' => ResU.Valid ρ' → rwpG (ℍ := ℍ) (Φ x)
      (erwpPostK (V x) (Tb x) Q (erwpCK (ℍ := ℍ) V Φ Tb Q n)) k ls' (Kc.plug w.1) ρ')
    (n := n) (ρ := ρ)
    (fun ℓ σ₁ σ₂ hp hc hv => erwpK_unfold_at hL (Nat.sub_le n 1) (h ℓ σ₁ σ₂ hp hc hv))
  rw [rwp_iff_rwpG] at ha
  exact rwpG_mono (fun _ _ _ _ ⟨⟨w, hw, hq⟩, hv⟩ => hw ▸ hq hv) (rwpG_validK ha)

/-- A release of an owned cell at an evaluation position, in front of an `erwpK` (`erwp_free`). -/
theorem erwpK_free {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι}
    (hL : ∀ x, (Tb x).Local) {Q : ι → PostN} {x : ι} (hΦ : (Φ x).Down) (Kc : Kont) (ℓ : Loc)
    (v : Val) {n : Nat} {ls : List SRec} {ρ : WRes}
    (h : (ptoOwn ℓ v ⋆ erwpK (ℍ := ℍ) V Φ Tb Q x (n - 1) ls (Kc.plug (.val v))) ρ) :
    erwpK (ℍ := ℍ) V Φ Tb Q x n ls (Kc.plug (BoLo.freeE (.val (Val.loc ℓ)))) ρ := by
  rw [erwpK_eq]
  refine rwpG_bind hΦ Kc ?_
  obtain ⟨ρ₁, ρ₂, hc, hp, hq⟩ := h
  have hf := rwp_free (ℍ := ℍ) (Φ := Φ x) ls ℓ v
    (fun k ls' w => rwpG (ℍ := ℍ) (Φ x) (erwpPostK (V x) (Tb x) Q (erwpCK (ℍ := ℍ) V Φ Tb Q n))
      k ls' (Kc.plug w.1)) (n := n) (ρ := ρ)
    ⟨ρ₁, ρ₂, hc, hp, erwpK_unfold_at hL (Nat.sub_le n 1) hq⟩
  rw [rwp_iff_rwpG] at hf
  exact rwpG_mono (fun _ _ _ _ ⟨w, hw, hq⟩ => hw ▸ hq) hf

/-- **The capture cell's allocation at `erwpK`**, the resource after it valid
(`erwp_kappaCell`). -/
theorem erwpK_kappaCellV {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι}
    (hL : ∀ x, (Tb x).Local) {Q : ι → PostN} {x : ι} (hΦ : (Φ x).Down) (hTd : (Tb x).Down)
    (hQ : ∀ y, (Q y).Down) (hasCancel : Bool) (H : Val) (K : Kont) (Kc : Kont) {n : Nat}
    {ls : List SRec} {ρ : WRes}
    (h : ∀ (ℓ : Loc) (σ₁ σ₂ : WRes), ptoOwn ℓ Val.unit σ₁ → ResU.CompS ρ σ₁ σ₂ →
      ResU.Valid σ₂ →
      erwpK (ℍ := ℍ) V Φ Tb Q x (n - 1) ls (Kc.plug (kappaC hasCancel ℓ H K)) σ₂) :
    erwpK (ℍ := ℍ) V Φ Tb Q x n ls (Kc.plug (kappaCell hasCancel H K)) ρ := by
  have e : Kc.plug (kappaCell hasCancel H K) =
      (Kc.comp (.appR (.val (.lam (BoLo.kappaCBody hasCancel H K))) .hole)).plug
        (.app (.val (.prim .alloc)) (.val Val.unit)) := by
    rw [Kont.plug_comp]; rfl
  rw [e]
  refine erwpK_allocV hL hΦ _ Val.unit (fun ℓ σ₁ σ₂ hp hc hv => ?_)
  rw [Kont.plug_comp]
  refine erwpK_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ (Val.loc ℓ)) rfl Kc) ?_
  rw [kappaCBody_subst]
  exact h ℓ σ₁ σ₂ hp hc hv

/-- **Resuming a `κ` that owns a cell, at `erwpK`** (`erwp_kappaC_resume`). -/
theorem erwpK_kappaC_resume {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι}
    (hL : ∀ x, (Tb x).Local) {Q : ι → PostN} {x : ι} (hΦ : (Φ x).Down) (hTd : (Tb x).Down)
    (hQ : ∀ y, (Q y).Down) (hasCancel : Bool) (ℓ : Loc) (H : Val) (K : Kont) (w : Val) {k : Nat}
    {ls : List SRec} {ρ : WRes}
    (h : (ptoOwn ℓ Val.unit ⋆
      erwpK (ℍ := ℍ) V Φ Tb Q x (k - 1) ls (hndE H (K.plug (.val w)))) ρ) :
    erwpK (ℍ := ℍ) V Φ Tb Q x k ls
      (.app (.app (kappaC hasCancel ℓ H K) (.val (Val.inj₁ .unit))) (.val w)) ρ := by
  refine erwpK_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.beta μ _ _) rfl (Kont.appL .hole w)) ?_
  refine erwpK_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl (Kont.appL .hole w)) ?_
  refine erwpK_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.seq μ _) rfl (Kont.appL .hole w)) ?_
  refine erwpK_free hL hΦ (Kont.appL (Kont.seq .hole _) w) ℓ Val.unit ?_
  obtain ⟨ρ₁, ρ₂, hc, hp, hq⟩ := h
  refine ⟨ρ₁, ρ₂, hc, hp, ?_⟩
  refine erwpK_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.seq μ _) rfl (Kont.appL .hole w)) ?_
  refine erwpK_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 1 + 1 : Nat) = 2 from rfl, kappa_resume_subst]
  exact hq

/-! ### Tables widened -/

/-- `FinLeSN` over a world index: a cancel obligation at least as weak, at every world. -/
def FinLeSK : Option (ι → Nat → List SRec → Expr → WProp) →
    Option (ι → Nat → List SRec → Expr → WProp) → Prop
  | _, none => True
  | none, some _ => False
  | some P, some P' => ∀ y k ls e ρ, P y k ls e ρ → P' y k ls e ρ

theorem finLeSK_apply {F F' : Option (ι → Nat → List SRec → Expr → WProp)} (h : FinLeSK F F')
    {P' : ι → Nat → List SRec → Expr → WProp} (hP' : F' = some P') {y : ι} {k : Nat}
    {ls : List SRec} {e : Expr} {ρ : WRes} (hF : ∀ P, F = some P → P y k ls e ρ) :
    P' y k ls e ρ := by
  subst hP'
  cases F with
  | none => exact h.elim
  | some P => exact h y k ls e ρ (hF P rfl)

theorem FinLeSK.refl : ∀ F : Option (ι → Nat → List SRec → Expr → WProp), FinLeSK F F
  | none => trivial
  | some _ => fun _ _ _ _ _ h => h

/-- `OpEntN.Le` over a world index: the wider entry owes its continuation at no more worlds. -/
def OpEntK.Le (en en' : OpEntK ι) : Prop :=
  en.q = en'.q ∧ en.abort = en'.abort ∧ en.PA = en'.PA ∧ en.PB = en'.PB ∧ en.wc = en'.wc ∧
    (∀ f y ρ, en'.wk f y ρ → en.wk f y ρ) ∧
    (en.abort = false → en.q ≠ .lin → FinLeSK en.fin en'.fin)

/-- `OpTabN.Le` over a world index. -/
def OpTabK.Le (T T' : OpTabK ι) : Prop :=
  ∀ n i en, T n i = some en → ∃ en', T' n i = some en' ∧ en.Le en'

theorem OpTabK.Sub.le {T T' : OpTabK ι} (h : T.Sub T') : T.Le T' := fun n i en hT =>
  ⟨en, h n i en hT, rfl, rfl, rfl, rfl, rfl, fun _ _ _ h => h, fun _ _ => FinLeSK.refl _⟩

/-- `OpTabN.Le` at the lifted tables. -/
theorem OpTabN.Le.liftK {T T' : OpTabN} (h : T.Le T') : (liftTabK T).Le (liftTabK T') := by
  intro m i en hT
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
  obtain ⟨en₀', h₀', hq, hab, hPA, hPB, hwc, hfl⟩ := h m i en₀ h₀
  refine ⟨liftEntK en₀', liftTabK_of_some h₀', hq, hab, hPA, ?_, hwc, fun _ _ _ _ => trivial,
    fun ha hq' => ?_⟩
  · simp only [liftEntK, hPB]
  · have := hfl ha hq'
    simp only [liftEntK]
    cases hf : en₀.fin with
    | none =>
        cases hf' : en₀'.fin with
        | none => trivial
        | some _ => rw [hf, hf'] at this; exact this.elim
    | some P =>
        cases hf' : en₀'.fin with
        | none => trivial
        | some P' =>
            rw [hf, hf'] at this
            exact fun _ k ls e ρ h => this k ls e ρ h

/-- **A stop of `opTableK lo T` is one of `opTableK lo T′` when `T ≤ T′`** (`opTableN_le`). -/
theorem opTableK_le {lo : Life} {T T' : OpTabK ι} (hT : T.Le T') :
    ∀ k ls t (Ψ Ψ' : ContK ι) ρ, (∀ y k', k' < k → ∀ ls e ρ, Ψ y k' ls e ρ → Ψ' y k' ls e ρ) →
      opTableK lo T k ls t Ψ ρ → opTableK lo T' k ls t Ψ' ρ := by
  intro k ls t Ψ Ψ' ρ hΨ h
  rcases opTableK_local lo T k ls t Ψ Ψ' ρ hΨ h with ⟨K, n, i, v, en, hp⟩ | ⟨K, n, i, v, en, hp⟩
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨en', h₃', hq, hab, hPA, hPB, hwc, hwk, hfl⟩ := hT n i en h₃
    refine Or.inl ⟨K, n, i, v, en', pure_sep_mk ⟨h₁, h₂, h₃', hab ▸ h₄⟩ ⟨ρa, ρk, hc, hPA ▸ hA,
      fun hu' => hu (hq.trans hu'), f, hf, fun y hy ls' he => ?_⟩⟩
    rw [← hwc] at he
    have hy' := hwk f y ρk hy
    refine ⟨fun k' hk' w => hPB ▸ (hcont y hy' ls' he).1 k' hk' w, fun hq' P hP => ?_⟩
    exact finLeSK_apply (hfl h₄ (hq ▸ hq')) hP
      (fun P₀ hP₀ => (hcont y hy' ls' he).2 (hq ▸ hq') P₀ hP₀)
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρn, hc, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    obtain ⟨en', h₃', -, hab, hPA', -⟩ := hT n i en h₃
    exact Or.inr ⟨K, n, i, v, en', pure_sep_mk ⟨h₁, h₂, h₃', hab ▸ h₄⟩
      ⟨ρa, ρn, hc, ⟨hPA' ▸ hPA, hnA⟩, hnn⟩⟩

/-- `opTableN_le` from `opTableK_le`. -/
theorem opTableN_le_of_K {T T' : OpTabN} (hT : T.Le T') :
    ∀ k ls t (Ψ Ψ' : ContN) ρ, (∀ k', k' < k → ∀ ls e ρ, Ψ k' ls e ρ → Ψ' k' ls e ρ) →
      opTableN T k ls t Ψ ρ → opTableN T' k ls t Ψ' ρ := by
  intro k ls t Ψ Ψ' ρ hΨ h
  have h' := (opTableK_liftTab 0 T k ls t (fun _ => Ψ) ρ).mpr h
  exact (opTableK_liftTab 0 T' k ls t (fun _ => Ψ') ρ).mp
    (opTableK_le hT.liftK k ls t _ _ ρ (fun _ k' hk' ls e ρ h => hΨ k' hk' ls e ρ h) h')

/-! ### Cancel runs -/

/-- **A cancel run caught at `ccatch`, at `erwpK`, the cancel run's table below the handler's, at
the worlds `Inv` holds at** (`erwp_ccatchLe`), the handler's table closed in the index there, by
induction on the index: the cancel's `raise` answers `()` at the run's own
world; a stop of the cancel run passes `ccatch` at the wider entry and the same floor, its
continuation re-entered at the resumption world. -/
theorem erwpK_ccatchLeI {V : ι → ι → Prop} (hV : ∀ y, V y y) {Φ : ι → LocFam} {Inv : ι → Prop}
    (hΦ : ∀ x, Inv x → (Φ x).Down) {fl : ι → Life} {T Tout : ι → OpTabK ι}
    (hT : ∀ z, (T z).Le (Tout z)) (hToutD : ∀ z, Inv z → (opTableK (fl z) (Tout z)).Down)
    (hInv : ∀ z m i en, Tout z m i = some en → en.abort = false → ∀ f y ρ, en.wk f y ρ → Inv y) :
    ∀ n x, Inv x → ∀ ls e ρ, erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T z)) (fun _ _ _ _ _ => False)
        x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) (fun _ => unitPost) x n ls
        (ccatchE e) ρ := by
  have hLin : ∀ z, (cancelTabK (fl z) (T z)).Local := fun z => cancelTabK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx ls e ρ h
  have hPD := erwpPostK_down (V := V x) (hToutD x hx)
    (Q := fun _ => unitPost) (fun _ => unitPost_down)
  rw [erwpK_eq]
  show rwpG (ℍ := ℍ) (Φ x) _ n ls (ccatchK.plug e) ρ
  refine rwpG_bind (hΦ x hx) ccatchK ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwpK_unfold_at hLin le_rfl h)
  rcases ht with ⟨_, _, _, _, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K', err, hs'⟩
  · exact hv.elim
  · -- an operation of a finaliser passes `ccatch`
    obtain ⟨⟨rfl, hK₁, hT₁, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    have hKo : (ccatchK.comp K₁).HasHnd m = false := by
      rw [hasHnd_comp, hK₁]; simp [Kont.HasHnd, Expr.val]
    have ht' : ccatchK.plug (K₁.plug (performE (.val (opPayload m i v)))) =
        (ccatchK.comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    obtain ⟨en', hT₁', hq, hab, hPA, hPB, hwc, hwk, hfl⟩ := hT x _ _ _ hT₁
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨ccatchK.comp K₁, m, i, v, en', pure_sep_mk ⟨rfl, hKo, hT₁', hab ▸ ha⟩
        ⟨ρa, ρk, hcak, hPA ▸ hA, fun hu' => hu (hq.trans hu'), f, hf, fun y hy ls'' he =>
          ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hq' => ?_⟩⟩⟩))
    · rw [← hwc] at he
      rw [Kont.plug_comp]
      have hc := (hcont y (hwk f y ρk hy) ls'' he).1 k' hk' w τ₁ τ₂ (hPB ▸ hB) hcτ
      simp only [erwpCK, show k' < n by omega, if_true] at hc ⊢
      exact ih k' (by omega) y (hInv x _ _ _ hT₁' (hab ▸ ha) f y ρk hy) _ _ _ hc
    · rw [← hwc] at he
      intro P hP
      show P y k ls'' ((ccatchK.comp K₁).dead.plug _) ρk
      rw [dead_comp, dead_ccatchK]
      exact finLeSK_apply (hfl ha (hq ▸ hq')) hP
        (fun P₀ hP₀ => (hcont y (hwk f y ρk hy) ls'' he).2 (hq ▸ hq') P₀ hP₀)
  · obtain ⟨⟨rfl, hK'⟩, τa, τb, hcab, he, hnb⟩ := pure_sep_iff.mp hs'
    cases err with
    | none =>
        refine rwpG_det (hΦ x hx) (hPD _)
          (fun μ => step1Only_plug (Head.cancel μ K' hK') rfl .hole) ?_
        have hτa : τa = PMap.empty := he.1
        subst hτa
        rw [← eq_of_compS_empty_left hcab] at hnb
        refine rwpG_garbage (rwpG_here (fun μ => final_val μ Val.unit)
          ⟨PMap.empty, σ, compS_empty_left σ, hnb, Or.inl ⟨Val.unit, rfl, x, hV x, rfl, rfl⟩⟩)
    | some E =>
        refine rwpG_det (hΦ x hx) (hPD _)
          (fun μ => step1Only_plug (Head.creraise μ E K' hK') rfl .hole) ?_
        obtain ⟨m, j, w, en, he⟩ := he
        obtain ⟨⟨rfl, hTe, ha⟩, hPA, hnA⟩ := pure_sep_iff.mp he
        obtain ⟨en', hTe', hle⟩ := hT x _ _ _ hTe
        have hfin : ∀ μ, Final (ℍ := ℍ) μ (Kont.hole.plug (opE true (opPayload m j w))) :=
          final_opPlug (payloadName_opPayload m j w) (by simp [OpFree, Kont.Catches])
        exact rwpG_here hfin (Or.inr (Or.inr ⟨.hole, m, j, w, en',
          pure_sep_mk ⟨rfl, rfl, hTe', hle.2.1 ▸ ha⟩ ⟨τa, τb, hcab, ⟨hle.2.2.1 ▸ hPA, hnA⟩, hnb⟩⟩))

/-- **A cancel run caught at `ccatch`, at `erwpK`, the cancel run's table below the handler's**:
`erwpK_ccatchLeI` with the handler's table closed in the index at every world. -/
theorem erwpK_ccatchLe {V : ι → ι → Prop} (hV : ∀ y, V y y) {Φ : ι → LocFam} {Inv : ι → Prop}
    (hΦ : ∀ x, Inv x → (Φ x).Down) {fl : ι → Life} {T Tout : ι → OpTabK ι}
    (hT : ∀ z, (T z).Le (Tout z)) (hToutD : ∀ z, (Tout z).Down)
    (hInv : ∀ z m i en, Tout z m i = some en → en.abort = false → ∀ f y ρ, en.wk f y ρ → Inv y) :
    ∀ n x, Inv x → ∀ ls e ρ, erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T z)) (fun _ _ _ _ _ => False)
        x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) (fun _ => unitPost) x n ls
        (ccatchE e) ρ :=
  erwpK_ccatchLeI hV hΦ hT (fun z _ => opTableK_down (hToutD z)) hInv

/-- **A cancel run caught at `ccatch`, at `erwpK`** (`erwp_ccatch`): `erwpK_ccatchLe` at a table
included in the handler's. -/
theorem erwpK_ccatch {V : ι → ι → Prop} (hV : ∀ y, V y y) {Φ : ι → LocFam} {Inv : ι → Prop}
    (hΦ : ∀ x, Inv x → (Φ x).Down) {fl : ι → Life} {T Tout : ι → OpTabK ι}
    (hT : ∀ z, (T z).Sub (Tout z)) (hToutD : ∀ z, (Tout z).Down)
    (hInv : ∀ z m i en, Tout z m i = some en → en.abort = false → ∀ f y ρ, en.wk f y ρ → Inv y) :
    ∀ n x, Inv x → ∀ ls e ρ, erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T z))
        (fun _ _ _ _ _ => False) x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) (fun _ => unitPost) x n ls
        (ccatchE e) ρ :=
  erwpK_ccatchLe hV hΦ (fun z => (hT z).le) hToutD hInv

/-- `erwp_ccatch` from `erwpK_ccatch`. -/
theorem erwp_ccatch_of_K {Φ : LocFam} (hΦ : Φ.Down) {T Tout : OpTabN} (hT : T.Sub Tout)
    (hToutD : Tout.Down) :
    ∀ n ls e ρ, cancelOblN (ℍ := ℍ) Φ T n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) unitPost n ls (ccatchE e) ρ := by
  intro n ls e ρ h
  rw [cancelOblN, erwp_eq_erwpK_of (cancelTabK_lift 0 T) Φ _] at h
  rw [erwp_opTableN_eq_erwpK 0]
  exact erwpK_ccatch (ℍ := ℍ) (V := fun _ _ => True) (fun _ => trivial) (Φ := fun _ => Φ)
    (Inv := fun _ => True) (fun _ _ => hΦ) (fl := fun _ => 0) (T := fun _ => liftTabK T)
    (Tout := fun _ => liftTabK Tout)
    (fun _ m i en h₁ => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
      exact liftTabK_of_some (hT m i en₀ h₀)) (fun _ => hToutD.liftK)
    (fun _ _ _ _ _ _ _ _ _ _ => trivial) n () trivial ls e ρ h

/-- Cancelling `κ` runs `ccatch (K†[raise …])`, at `erwpK` (`erwp_kappa_cancel`). -/
theorem erwpK_kappa_cancel {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι}
    {Q : ι → PostN} {x : ι} (hΦ : (Φ x).Down) (hTd : (Tb x).Down) (hQ : ∀ y, (Q y).Down)
    (H : Val) (K : Kont) {k : Nat} {ls : List SRec} {ρ : WRes}
    (h : erwpK (ℍ := ℍ) V Φ Tb Q x k ls
      (ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))) ρ) :
    erwpK (ℍ := ℍ) V Φ Tb Q x k ls (.app (kappa H K) (.val (Val.inj₂ .unit))) ρ := by
  refine erwpK_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  refine erwpK_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
  refine erwpK_det hΦ hTd hQ (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, kappa_cancel_subst]
  exact h

/-- **Cancelling a cancellable `κ`**, at `erwpK` (`erwp_kappaC_cancel`). -/
theorem erwpK_kappaC_cancel {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι}
    (hL : ∀ x, (Tb x).Local) {Q : ι → PostN} {x : ι} (hΦ : (Φ x).Down) (hTd : (Tb x).Down)
    (hQ : ∀ y, (Q y).Down) (ℓ : Loc) (H : Val) (K : Kont) {k : Nat} {ls : List SRec} {ρ : WRes}
    (h : (ptoOwn ℓ Val.unit ⋆ erwpK (ℍ := ℍ) V Φ Tb Q x (k - 1) ls
      (ccatchE (K.dead.plug (raiseE (.val (cancelVal none)))))) ρ) :
    erwpK (ℍ := ℍ) V Φ Tb Q x k ls (.app (kappaC true ℓ H K) (.val (Val.inj₂ .unit))) ρ := by
  refine erwpK_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  refine erwpK_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
  refine erwpK_det hΦ hTd hQ (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  refine erwpK_free hL hΦ (Kont.seq .hole _) ℓ Val.unit ?_
  obtain ⟨ρ₁, ρ₂, hc, hp, hq⟩ := h
  refine ⟨ρ₁, ρ₂, hc, hp, ?_⟩
  refine erwpK_det hΦ hTd hQ (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, kappa_cancel_subst]
  exact hq

/-! ### The handler -/

/-- **A handler at `erwpK`, its clauses asked at the stops up to `N`, each cancel row's table below
the cancel table, at the worlds `Inv` holds at** (`erwp_handle_le` with `OpTabK.Le`), the tables
closed in the index there, by induction on the index. A clause at the handler's name receives the stopped run's Kripke stop
(`KapRelK`) at the floor the stop chose, owed at every world the entry allows there; it is read
at the clause's own world. A value of the handled run is posted at a world the post order allows;
the return clause runs there. The table of the handled run and the handler's agree off the
handler's name (`hTin`), and the post order allows no more stops of the handler's table
(`hTV`). -/
theorem erwpK_handleLe_leI {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    {Φ : ι → LocFam} {Inv : ι → Prop} (hΦ : ∀ x, Inv x → (Φ x).Down)
    (hΦV : ∀ x y, V x y → Φ y = Φ x) {fl : ι → Life}
    (N : Nat) (Tin Tout : ι → OpTabK ι) (hTinD : ∀ x, Inv x → (Tin x).DownAt Inv)
    (hTout : ∀ x, Inv x → (opTableK (fl x) (Tout x)).Down)
    (hTV : ∀ x y, V x y → (opTableK (fl y) (Tout y)).Le (opTableK (fl x) (Tout x)))
    (n₀ : UInt32) (hTin : ∀ x m i, m ≠ n₀ → Tin x m i = Tout x m i) (qs hr hs : Val)
    (Qin Qout : ι → PostN) (hQout : ∀ x, (Qout x).Down)
    (hq : ∀ x i en, Tin x n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag)
    (hwcl : ∀ x m i en, Tin x m i = some en → ∀ ls ls' (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
      en.wc ls ls' ρ → en.wc ls ls' ρ₁)
    (hwk : ∀ x i en, Tin x n₀ i = some en → en.abort = false → ∀ f y (ρ₁ ρ₂ ρ : WRes),
      ResU.CompS ρ₁ ρ₂ ρ → ResU.Valid ρ → en.wk f y ρ → en.wk f y ρ₁)
    (Tc : UInt32 → Option (ι → OpTabK ι))
    (hTc : ∀ x i en, Tin x n₀ i = some en → en.abort = false → en.q ≠ .lin → ∀ Tk,
      Tc i = some Tk → ∃ T₁ : ι → OpTabK ι,
        en.fin = some (fun y k ls e => erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T₁ z))
          (fun _ _ _ _ _ => False) y k ls e) ∧ (∀ z, (T₁ z).Le (Tk z)) ∧
          ∀ z, Inv z → (opTableK (fl z) (Tk z)).Down)
    (hVr : ∀ y, V y y)
    (hInvW : ∀ x m i en, Tin x m i = some en → en.abort = false → ∀ f y ρ, en.wk f y ρ → Inv y)
    (hInvC : ∀ i Tk, Tc i = some Tk → ∀ z m j en, Tk z m j = some en → en.abort = false →
      ∀ f y ρ, en.wk f y ρ → Inv y)
    (hret : ∀ x k, k ≤ N → ∀ ls v ρ, Qin x k ls v ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
        (.app (.val hr) (.val v)) ρ)
    (hop : ∀ x i en, Tin x n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ k, k ≤ N → ∀ ls v (κ : Val) ρ,
        (en.PA k ls v ⋆ KapRelK (ℍ := ℍ) V Φ fl (fun z => opTableK (fl z) (Tout z)) Qout en
          (fl x) (Tc i) k ls κ) ρ →
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
          (.app (.val c) (.pair (.val v) κ.1)) ρ) ∧
      (en.abort = true → ∀ k, k ≤ N → ∀ ls v ρ, en.PA k ls v ρ →
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
          (.app (.val c) (.val v)) ρ)) :
    ∀ n, n ≤ N → ∀ x, Inv x → ∀ ls e ρ,
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tin z)) Qin x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x n ls
        (hndE (hndVal n₀ qs hr hs) e) ρ := by
  have hLin : ∀ z, (opTableK (fl z) (Tin z)).Local := fun z => opTableK_local _ _
  have hLout : ∀ z, (opTableK (fl z) (Tout z)).Local := fun z => opTableK_local _ _
  have hDout : ∀ z, Inv z → (opTableK (fl z) (Tout z)).Down := hTout
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN x hx ls e ρ h
  have hPD := erwpPostK_down (V := V x) (hDout x hx) hQout
  set H := hndVal n₀ qs hr hs with hH
  rw [erwpK_eq]
  show rwpG (ℍ := ℍ) (Φ x) _ n ls ((hndK H).plug e) ρ
  refine rwpG_bind (hΦ x hx) (hndK H) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ⟨ht, hvσ⟩ => ?_)
    (rwpG_validK (erwpK_unfold_at hLin le_rfl h))
  -- what the continuations of the handled run are owed, read through the induction hypothesis
  have hcontIH : ∀ y, Inv y → ∀ k', k' < k → ∀ ls'' e'' τ,
      erwpCK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tin z)) Qin n y k' ls'' e'' τ →
      erwpCK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout n y k' ls'' (hndE H e'') τ := by
    intro y hyI k' hk' ls'' e'' τ hc
    simp only [erwpCK, show k' < n by omega, if_true] at hc ⊢
    exact ih k' (by omega) (by omega) y hyI ls'' e'' τ hc
  rcases ht with ⟨v, rfl, y, hy, hv⟩ | ht | ht
  · -- `[ret]`, at the world the handled run's value is posted at
    exact rwpG_det (hΦ x hx) (hPD _)
      (fun μ => step1Only_plug (Head.hret μ n₀ qs hr hs v) rfl .hole)
      (erwpK_shift hVt hΦV hTV hLout hy hk (hret y k (by omega) ls' v σ hv))
  · -- a stop at a non-abortive operation
    obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    by_cases hm : m = n₀
    · -- `[op]` at the handler's name: the clause, with the Kripke stop
      subst hm
      obtain ⟨c, hc, hna, -⟩ := hop x i en hT
      refine rwpG_det (hΦ x hx) (hPD _)
        (fun μ => step1Only_plug (Head.hop μ m i qs hr hs c v K₁ hc hK₁) rfl .hole) ?_
      -- the cancel run of the continuation at a world, at the cancel row's table
      have hcan : ∀ y, Inv y → ∀ (ρ' : WRes), ∀ ls'', en.wc ls' ls'' ρ' →
          (en.q ≠ .lin → cancelOKK en y k ls'' K₁ ρ') → en.q ≠ .lin → ∀ Tk, Tc i = some Tk →
          ∀ k'', k'' ≤ k →
          erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tk z)) (fun _ => unitPost) y k'' ls''
            (ccatchE (K₁.dead.plug (raiseE (.val (cancelVal none))))) ρ' := by
        intro y hyI ρ' ls'' _ hco hq' Tk hTk k'' hk''
        obtain ⟨T₁, hfn, hsub, hTkD⟩ := hTc x i en hT ha hq' Tk hTk
        have hP := hco hq' _ hfn
        exact erwpK_ccatchLeI hVr hΦ hsub hTkD (hInvC i Tk hTk) k'' y hyI ls'' _ ρ'
          ((hTinD x hx).fin_le hT hfn hyI hk'' hP)
      have hDk : ∀ Tk : ι → OpTabK ι, Tc i = some Tk → en.q ≠ .lin → ∀ z, Inv z →
          (opTableK (fl z) (Tk z)).Down := by
        intro Tk hTk hq' z hz
        obtain ⟨-, -, -, hTkD⟩ := hTc x i en hT ha hq' Tk hTk
        exact hTkD z hz
      rw [hq x i en hT ha, kappaAt_tag]
      cases hqq : en.q with
      | unr =>
          refine erwpK_unfold_at hLout hk (hna ha k (by omega) ls' v
            ⟨kappa H K₁, by unfold kappa; exact .lam⟩ σ ⟨ρa, ρk, hcak, hA, hu, f, hf, ?_⟩)
          intro y hy ls'' he k' hk'
          have hyI := hInvW x _ i en hT ha f y ρk hy
          refine ⟨fun w τ₁ τ₂ hB hcτ => ?_, fun hq' Tk hTk => ?_⟩
          · have h₁ := hcontIH y hyI k' hk' _ _ _
              ((hcont y hy ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ)
            simp only [erwpCK, show k' < n by omega, if_true] at h₁
            exact erwpK_kappa_resume (hΦ y hyI) (hDout y hyI) hQout H K₁ w h₁
          · exact erwpK_kappa_cancel (hΦ y hyI) (hDk Tk hTk hq' y hyI) (fun _ => unitPost_down) H K₁
              (hcan y hyI ρk ls'' he (hcont y hy ls'' he).2 hq' Tk hTk k' (by omega))
      | lin | cancel =>
          -- the cell is allocated, one step; `κ` is `kappaC` at it, owning the cell and the share
          refine erwpK_unfold_at hLout hk (erwpK_kappaCellV hLout (hΦ x hx) (hDout x hx) hQout _ H K₁
            (.appR (.val c) (.pairR v .hole)) (fun ℓ σ₁ σ₂ hcell hc₂ hv₂ => ?_))
          obtain ⟨y₀, hy₁, hy₂⟩ := compS_reassoc hcak hc₂
          have hvy : ResU.Valid y₀ := (ResU.Valid.split hy₂ hv₂).2
          have hA' : en.PA (k - 1) ls' v ρa := by
            cases k with
            | zero => exact hA
            | succ k₀ => exact (hTinD x hx).pa _ _ _ hT _ _ _ _ hA
          refine hna ha (k - 1) (by omega) ls' v ⟨_, isVal_kappaC _ ℓ H K₁⟩ σ₂
            ⟨ρa, y₀, hy₂, hA', fun hq' => absurd (hqq.symm.trans hq') (by simp), f, hf, ?_⟩
          intro y hy ls'' he k' hk'
          have hyk : en.wk f y ρk := hwk x i en hT ha f y ρk σ₁ y₀ hy₁ hvy hy
          have hek : en.wc ls' ls'' ρk := hwcl x _ _ _ hT _ _ _ _ _ hy₁ he
          have hyI := hInvW x _ i en hT ha f y ρk hyk
          refine ⟨fun w τ₁ τ₂ hB hcτ => ?_, fun hq' Tk hTk => ?_⟩
          · obtain ⟨z, hz, hzτ⟩ := compS_exch hy₁ hcτ
            have h₁ := hcontIH y hyI k' (by omega) _ _ _
              ((hcont y hyk ls'' hek).1 k' (by omega) w τ₁ z hB hz)
            simp only [erwpCK, show k' < n by omega, if_true] at h₁
            exact erwpK_kappaC_resume hLout (hΦ y hyI) (hDout y hyI) hQout _ ℓ H K₁ w
              ⟨σ₁, z, ResU.CompS.comm hzτ, hcell,
                erwpK_le (hΦ y hyI) hLout (hDout y hyI) hQout (Nat.sub_le k' 1) h₁⟩
          · first
              | exact absurd hqq hq'
              | exact erwpK_kappaC_cancel (fun z => opTableK_local _ _) (hΦ y hyI)
                  (hDk Tk hTk hq' y hyI)
                  (fun _ => unitPost_down) ℓ H K₁ ⟨σ₁, ρk, ResU.CompS.comm hy₁, hcell,
                    hcan y hyI ρk ls'' hek (hcont y hyk ls'' hek).2 hq' Tk hTk (k' - 1)
                      (by omega)⟩
    · -- an operation of another name passes outward, at the same entry and floor
      have hKo : ((hndK H).comp K₁).HasHnd m = false := by
        rw [hasHnd_comp, hndK_hasHnd, hK₁]; simpa using Ne.symm hm
      have ht' : (hndK H).plug (K₁.plug (performE (.val (opPayload m i v)))) =
          ((hndK H).comp K₁).plug (opE false (opPayload m i v)) := by
        rw [Kont.plug_comp]; rfl
      rw [ht']
      refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
        ⟨(hndK H).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, (hTin x m i hm) ▸ hT, ha⟩
          ⟨ρa, ρk, hcak, hA, hu, f, hf, fun y hy ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
            fun hq' => ?_⟩⟩⟩))
      · rw [Kont.plug_comp]
        exact hcontIH y (hInvW x m i en hT ha f y ρk hy) k' hk' _ _ _
          ((hcont y hy ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ)
      · intro P hP
        show P y k ls'' (((hndK H).comp K₁).dead.plug _) ρk
        rw [dead_comp, dead_hndK]
        exact (hcont y hy ls'' he).2 hq' P hP
  · -- a stop at an abortive operation
    obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    by_cases hm : m = n₀
    · -- `[unwind]` at the handler's name: the clause; the continuation is discarded
      subst hm
      obtain ⟨c, hc, -, hab⟩ := hop x i en hT
      refine rwpG_det (hΦ x hx) (hPD _)
        (fun μ => step1Only_plug (Head.hunwind μ m i qs hr hs c v K₁ hc hK₁) rfl .hole) ?_
      refine rwpG_garbage (rwpG_mono (fun _ _ _ _ ⟨τ₁, τ₂, hcτ, hq', hnτ⟩ =>
        ⟨τ₁, τ₂, hcτ, hnτ, hq'⟩) (rwpG_frame (fun _ τ => NoOwn τ) (fun _ _ _ _ h => h) hcan
          (erwpK_unfold_at hLout hk (hab ha k (by omega) ls' v ρa hPA)) hnn))
    · -- an abortive operation of another name passes outward
      have hKo : ((hndK H).comp K₁).Catches m = false := by
        rw [catches_comp, hndK_catches, hK₁]; simpa using Ne.symm hm
      have ht' : (hndK H).plug (K₁.plug (raiseE (.val (opPayload m i v)))) =
          ((hndK H).comp K₁).plug (opE true (opPayload m i v)) := by
        rw [Kont.plug_comp]; rfl
      rw [ht']
      exact rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
        ⟨(hndK H).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, (hTin x m i hm) ▸ hT, ha⟩
          ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩⟩))

/-- **A handler at `erwpK`, its clauses asked at the stops up to `N`, each cancel row's table below
the cancel table** (`erwp_handle_le` with `OpTabK.Le`): `erwpK_handleLe_leI` with the tables closed
in the index at every world. -/
theorem erwpK_handleLe_le {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    {Φ : ι → LocFam} {Inv : ι → Prop} (hΦ : ∀ x, Inv x → (Φ x).Down)
    (hΦV : ∀ x y, V x y → Φ y = Φ x) {fl : ι → Life}
    (N : Nat) (Tin Tout : ι → OpTabK ι) (hTinD : ∀ x, (Tin x).Down)
    (hTout : ∀ x, (Tout x).Down)
    (hTV : ∀ x y, V x y → (opTableK (fl y) (Tout y)).Le (opTableK (fl x) (Tout x)))
    (n₀ : UInt32) (hTin : ∀ x m i, m ≠ n₀ → Tin x m i = Tout x m i) (qs hr hs : Val)
    (Qin Qout : ι → PostN) (hQout : ∀ x, (Qout x).Down)
    (hq : ∀ x i en, Tin x n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag)
    (hwcl : ∀ x m i en, Tin x m i = some en → ∀ ls ls' (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
      en.wc ls ls' ρ → en.wc ls ls' ρ₁)
    (hwk : ∀ x i en, Tin x n₀ i = some en → en.abort = false → ∀ f y (ρ₁ ρ₂ ρ : WRes),
      ResU.CompS ρ₁ ρ₂ ρ → ResU.Valid ρ → en.wk f y ρ → en.wk f y ρ₁)
    (Tc : UInt32 → Option (ι → OpTabK ι))
    (hTc : ∀ x i en, Tin x n₀ i = some en → en.abort = false → en.q ≠ .lin → ∀ Tk,
      Tc i = some Tk → ∃ T₁ : ι → OpTabK ι,
        en.fin = some (fun y k ls e => erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T₁ z))
          (fun _ _ _ _ _ => False) y k ls e) ∧ (∀ z, (T₁ z).Le (Tk z)) ∧ ∀ z, (Tk z).Down)
    (hVr : ∀ y, V y y)
    (hInvW : ∀ x m i en, Tin x m i = some en → en.abort = false → ∀ f y ρ, en.wk f y ρ → Inv y)
    (hInvC : ∀ i Tk, Tc i = some Tk → ∀ z m j en, Tk z m j = some en → en.abort = false →
      ∀ f y ρ, en.wk f y ρ → Inv y)
    (hret : ∀ x k, k ≤ N → ∀ ls v ρ, Qin x k ls v ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
        (.app (.val hr) (.val v)) ρ)
    (hop : ∀ x i en, Tin x n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ k, k ≤ N → ∀ ls v (κ : Val) ρ,
        (en.PA k ls v ⋆ KapRelK (ℍ := ℍ) V Φ fl (fun z => opTableK (fl z) (Tout z)) Qout en
          (fl x) (Tc i) k ls κ) ρ →
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
          (.app (.val c) (.pair (.val v) κ.1)) ρ) ∧
      (en.abort = true → ∀ k, k ≤ N → ∀ ls v ρ, en.PA k ls v ρ →
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
          (.app (.val c) (.val v)) ρ)) :
    ∀ n, n ≤ N → ∀ x, Inv x → ∀ ls e ρ,
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tin z)) Qin x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x n ls
        (hndE (hndVal n₀ qs hr hs) e) ρ :=
  erwpK_handleLe_leI hVt hΦ hΦV N Tin Tout (fun x _ => (hTinD x).downAt Inv)
    (fun x _ => opTableK_down (hTout x)) hTV n₀ hTin qs hr hs Qin Qout hQout hq hwcl hwk Tc
    (fun x i en hT ha hq' Tk hTk => by
      obtain ⟨T₁, hf, hsub, hTkD⟩ := hTc x i en hT ha hq' Tk hTk
      exact ⟨T₁, hf, hsub, fun z _ => opTableK_down (hTkD z)⟩) hVr hInvW hInvC hret hop

/-- **A handler at `erwpK`, its clauses asked at the stops up to `N`, at the worlds `Inv` holds
at** (`erwp_handle_le`): `erwpK_handleLe_leI` at cancel tables included in the handler's, the
tables closed in the index at the worlds `Inv` holds at. -/
theorem erwpK_handle_leI {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    {Φ : ι → LocFam} {Inv : ι → Prop} (hΦ : ∀ x, Inv x → (Φ x).Down)
    (hΦV : ∀ x y, V x y → Φ y = Φ x) {fl : ι → Life}
    (N : Nat) (Tin Tout : ι → OpTabK ι) (hTinD : ∀ x, Inv x → (Tin x).DownAt Inv)
    (hTout : ∀ x, Inv x → (opTableK (fl x) (Tout x)).Down)
    (hTV : ∀ x y, V x y → (opTableK (fl y) (Tout y)).Le (opTableK (fl x) (Tout x)))
    (n₀ : UInt32) (hTin : ∀ x m i, m ≠ n₀ → Tin x m i = Tout x m i) (qs hr hs : Val)
    (Qin Qout : ι → PostN) (hQout : ∀ x, (Qout x).Down)
    (hq : ∀ x i en, Tin x n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag)
    (hwcl : ∀ x m i en, Tin x m i = some en → ∀ ls ls' (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
      en.wc ls ls' ρ → en.wc ls ls' ρ₁)
    (hwk : ∀ x i en, Tin x n₀ i = some en → en.abort = false → ∀ f y (ρ₁ ρ₂ ρ : WRes),
      ResU.CompS ρ₁ ρ₂ ρ → ResU.Valid ρ → en.wk f y ρ → en.wk f y ρ₁)
    (Tc : UInt32 → Option (ι → OpTabK ι))
    (hTc : ∀ x i en, Tin x n₀ i = some en → en.abort = false → en.q ≠ .lin → ∀ Tk,
      Tc i = some Tk → ∃ T₁ : ι → OpTabK ι,
        en.fin = some (fun y k ls e => erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T₁ z))
          (fun _ _ _ _ _ => False) y k ls e) ∧ (∀ z, (T₁ z).Sub (Tk z)) ∧
          ∀ z, Inv z → (opTableK (fl z) (Tk z)).Down)
    (hVr : ∀ y, V y y)
    (hInvW : ∀ x m i en, Tin x m i = some en → en.abort = false → ∀ f y ρ, en.wk f y ρ → Inv y)
    (hInvC : ∀ i Tk, Tc i = some Tk → ∀ z m j en, Tk z m j = some en → en.abort = false →
      ∀ f y ρ, en.wk f y ρ → Inv y)
    (hret : ∀ x k, k ≤ N → ∀ ls v ρ, Qin x k ls v ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
        (.app (.val hr) (.val v)) ρ)
    (hop : ∀ x i en, Tin x n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ k, k ≤ N → ∀ ls v (κ : Val) ρ,
        (en.PA k ls v ⋆ KapRelK (ℍ := ℍ) V Φ fl (fun z => opTableK (fl z) (Tout z)) Qout en
          (fl x) (Tc i) k ls κ) ρ →
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
          (.app (.val c) (.pair (.val v) κ.1)) ρ) ∧
      (en.abort = true → ∀ k, k ≤ N → ∀ ls v ρ, en.PA k ls v ρ →
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
          (.app (.val c) (.val v)) ρ)) :
    ∀ n, n ≤ N → ∀ x, Inv x → ∀ ls e ρ,
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tin z)) Qin x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x n ls
        (hndE (hndVal n₀ qs hr hs) e) ρ :=
  erwpK_handleLe_leI hVt hΦ hΦV N Tin Tout hTinD hTout hTV n₀ hTin qs hr hs Qin Qout hQout hq hwcl
    hwk Tc (fun x i en hT ha hq' Tk hTk => by
      obtain ⟨T₁, hf, hsub, hTkD⟩ := hTc x i en hT ha hq' Tk hTk
      exact ⟨T₁, hf, fun z => (hsub z).le, hTkD⟩) hVr hInvW hInvC hret hop

/-- **A handler at `erwpK`, its clauses asked at the stops up to `N`** (`erwp_handle_le`):
`erwpK_handle_leI` with the tables closed in the index at every world. -/
theorem erwpK_handle_le {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    {Φ : ι → LocFam} {Inv : ι → Prop} (hΦ : ∀ x, Inv x → (Φ x).Down)
    (hΦV : ∀ x y, V x y → Φ y = Φ x) {fl : ι → Life}
    (N : Nat) (Tin Tout : ι → OpTabK ι) (hTinD : ∀ x, (Tin x).Down)
    (hTout : ∀ x, (Tout x).Down)
    (hTV : ∀ x y, V x y → (opTableK (fl y) (Tout y)).Le (opTableK (fl x) (Tout x)))
    (n₀ : UInt32) (hTin : ∀ x m i, m ≠ n₀ → Tin x m i = Tout x m i) (qs hr hs : Val)
    (Qin Qout : ι → PostN) (hQout : ∀ x, (Qout x).Down)
    (hq : ∀ x i en, Tin x n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag)
    (hwcl : ∀ x m i en, Tin x m i = some en → ∀ ls ls' (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
      en.wc ls ls' ρ → en.wc ls ls' ρ₁)
    (hwk : ∀ x i en, Tin x n₀ i = some en → en.abort = false → ∀ f y (ρ₁ ρ₂ ρ : WRes),
      ResU.CompS ρ₁ ρ₂ ρ → ResU.Valid ρ → en.wk f y ρ → en.wk f y ρ₁)
    (Tc : UInt32 → Option (ι → OpTabK ι))
    (hTc : ∀ x i en, Tin x n₀ i = some en → en.abort = false → en.q ≠ .lin → ∀ Tk,
      Tc i = some Tk → ∃ T₁ : ι → OpTabK ι,
        en.fin = some (fun y k ls e => erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T₁ z))
          (fun _ _ _ _ _ => False) y k ls e) ∧ (∀ z, (T₁ z).Sub (Tk z)) ∧ ∀ z, (Tk z).Down)
    (hVr : ∀ y, V y y)
    (hInvW : ∀ x m i en, Tin x m i = some en → en.abort = false → ∀ f y ρ, en.wk f y ρ → Inv y)
    (hInvC : ∀ i Tk, Tc i = some Tk → ∀ z m j en, Tk z m j = some en → en.abort = false →
      ∀ f y ρ, en.wk f y ρ → Inv y)
    (hret : ∀ x k, k ≤ N → ∀ ls v ρ, Qin x k ls v ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
        (.app (.val hr) (.val v)) ρ)
    (hop : ∀ x i en, Tin x n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ k, k ≤ N → ∀ ls v (κ : Val) ρ,
        (en.PA k ls v ⋆ KapRelK (ℍ := ℍ) V Φ fl (fun z => opTableK (fl z) (Tout z)) Qout en
          (fl x) (Tc i) k ls κ) ρ →
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
          (.app (.val c) (.pair (.val v) κ.1)) ρ) ∧
      (en.abort = true → ∀ k, k ≤ N → ∀ ls v ρ, en.PA k ls v ρ →
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
          (.app (.val c) (.val v)) ρ)) :
    ∀ n, n ≤ N → ∀ x, Inv x → ∀ ls e ρ,
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tin z)) Qin x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x n ls
        (hndE (hndVal n₀ qs hr hs) e) ρ :=
  erwpK_handle_leI hVt hΦ hΦV N Tin Tout (fun x _ => (hTinD x).downAt Inv)
    (fun x _ => opTableK_down (hTout x)) hTV n₀ hTin qs hr hs Qin Qout hQout hq hwcl hwk Tc
    (fun x i en hT ha hq' Tk hTk => by
      obtain ⟨T₁, hf, hsub, hTkD⟩ := hTc x i en hT ha hq' Tk hTk
      exact ⟨T₁, hf, hsub, fun z _ => opTableK_down (hTkD z)⟩) hVr hInvW hInvC hret hop

/-- **A handler at `erwpK`** (`erwp_handle`): `erwpK_handle_le` at `N = n`. -/
theorem erwpK_handle {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    {Φ : ι → LocFam} {Inv : ι → Prop} (hΦ : ∀ x, Inv x → (Φ x).Down)
    (hΦV : ∀ x y, V x y → Φ y = Φ x) {fl : ι → Life}
    (Tin Tout : ι → OpTabK ι) (hTinD : ∀ x, (Tin x).Down) (hTout : ∀ x, (Tout x).Down)
    (hTV : ∀ x y, V x y → (opTableK (fl y) (Tout y)).Le (opTableK (fl x) (Tout x)))
    (n₀ : UInt32) (hTin : ∀ x m i, m ≠ n₀ → Tin x m i = Tout x m i) (qs hr hs : Val)
    (Qin Qout : ι → PostN) (hQout : ∀ x, (Qout x).Down)
    (hq : ∀ x i en, Tin x n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag)
    (hwcl : ∀ x m i en, Tin x m i = some en → ∀ ls ls' (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
      en.wc ls ls' ρ → en.wc ls ls' ρ₁)
    (hwk : ∀ x i en, Tin x n₀ i = some en → en.abort = false → ∀ f y (ρ₁ ρ₂ ρ : WRes),
      ResU.CompS ρ₁ ρ₂ ρ → ResU.Valid ρ → en.wk f y ρ → en.wk f y ρ₁)
    (Tc : UInt32 → Option (ι → OpTabK ι))
    (hTc : ∀ x i en, Tin x n₀ i = some en → en.abort = false → en.q ≠ .lin → ∀ Tk,
      Tc i = some Tk → ∃ T₁ : ι → OpTabK ι,
        en.fin = some (fun y k ls e => erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T₁ z))
          (fun _ _ _ _ _ => False) y k ls e) ∧ (∀ z, (T₁ z).Sub (Tk z)) ∧ ∀ z, (Tk z).Down)
    (hVr : ∀ y, V y y)
    (hInvW : ∀ x m i en, Tin x m i = some en → en.abort = false → ∀ f y ρ, en.wk f y ρ → Inv y)
    (hInvC : ∀ i Tk, Tc i = some Tk → ∀ z m j en, Tk z m j = some en → en.abort = false →
      ∀ f y ρ, en.wk f y ρ → Inv y)
    (hret : ∀ x k ls v ρ, Qin x k ls v ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
        (.app (.val hr) (.val v)) ρ)
    (hop : ∀ x i en, Tin x n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ k ls v (κ : Val) ρ,
        (en.PA k ls v ⋆ KapRelK (ℍ := ℍ) V Φ fl (fun z => opTableK (fl z) (Tout z)) Qout en
          (fl x) (Tc i) k ls κ) ρ →
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
          (.app (.val c) (.pair (.val v) κ.1)) ρ) ∧
      (en.abort = true → ∀ k ls v ρ, en.PA k ls v ρ →
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
          (.app (.val c) (.val v)) ρ)) :
    ∀ n x, Inv x → ∀ ls e ρ,
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tin z)) Qin x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x n ls
        (hndE (hndVal n₀ qs hr hs) e) ρ :=
  fun n => erwpK_handle_le hVt hΦ hΦV n Tin Tout hTinD hTout hTV n₀ hTin qs hr hs Qin Qout hQout
    hq hwcl hwk Tc hTc hVr hInvW hInvC (fun x k _ => hret x k)
    (fun x i en hT => by
      obtain ⟨c, hc, h₁, h₂⟩ := hop x i en hT
      exact ⟨c, hc, fun ha k _ => h₁ ha k, fun ha k _ => h₂ ha k⟩) n le_rfl

/-! ### The scheduler's `[handle]` -/

/-- **The scheduler's `[handle]` at `erwpK`**: a scheduler meeting the contract at `erwpK`
(`SchedOKNLeK`) is a handler of its name at the empty outer table, every stopped task received as
its Kripke stop at the floor the task's stop chose. The entries' order at `κ`'s share is read at the
part the stop left (`hwk`). -/
theorem erwpK_handle_sched {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    (hVr : ∀ y, V y y) {Φ : ι → LocFam} {Inv : ι → Prop} (hΦ : ∀ x, Inv x → (Φ x).Down)
    (hΦV : ∀ x y, V x y → Φ y = Φ x) {fl : ι → Life}
    (hTV : ∀ x y, V x y → (opTableK (fl y) (OpTabK.empty : OpTabK ι)).Le
      (opTableK (fl x) OpTabK.empty))
    {N : Nat} {T : ι → OpTabK ι} {n₀ : UInt32} {qs hr hs : Val} {Qin Qout : ι → PostN}
    (hS : SchedOKNLeK (ℍ := ℍ) V Φ fl N T n₀ qs hr hs Qin Qout)
    (hwk : ∀ x i en, T x n₀ i = some en → en.abort = false → ∀ f y (ρ₁ ρ₂ ρ : WRes),
      ResU.CompS ρ₁ ρ₂ ρ → ResU.Valid ρ → en.wk f y ρ → en.wk f y ρ₁)
    (hInvW : ∀ x m i en, T x m i = some en → en.abort = false → ∀ f y ρ, en.wk f y ρ → Inv y) :
    ∀ n, n ≤ N → ∀ x, Inv x → ∀ ls e ρ,
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Qin x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) OpTabK.empty) Qout x n ls
        (hndE (hndVal n₀ qs hr hs) e) ρ :=
  erwpK_handle_le hVt hΦ hΦV N T (fun _ => OpTabK.empty) hS.down (fun _ => ⟨fun _ _ _ h => by simp [OpTabK.empty] at h,
      fun _ _ _ _ h => by simp [OpTabK.empty] at h⟩) hTV n₀
    (fun x m i hm => hS.names x m i hm) qs hr hs Qin Qout hS.qdown hS.tags hS.wcl hwk
    (fun _ => some T)
    (fun x i en hT ha hq Tk hTk => by
      cases Option.some.inj hTk
      obtain ⟨T₁, hf, hsub⟩ := hS.fin x i en hT ha hq
      exact ⟨T₁, hf, hsub, hS.down⟩) hVr hInvW
    (fun i Tk hTk => by cases Option.some.inj hTk; exact hInvW) hS.ret hS.op

/-- **The scheduler's `[handle]` at the typed world**: `erwpK_handle_sched` at `KW`, posts at the
run's own world. -/
theorem erwpK_handle_schedKW {N : Nat} {T : KW → OpTabK KW} {n₀ : UInt32} {qs hr hs : Val}
    {Qin Qout : KW → PostN}
    (hS : SchedOKNLeK (ℍ := ℍ) KW.PostK (fun x => x.Θ.view x.c) (fun x => x.lo) N T n₀ qs hr hs
      Qin Qout)
    (hwk : ∀ x i en, T x n₀ i = some en → en.abort = false → ∀ f y (ρ₁ ρ₂ ρ : WRes),
      ResU.CompS ρ₁ ρ₂ ρ → ResU.Valid ρ → en.wk f y ρ → en.wk f y ρ₁)
    (hOK : ∀ x m i en, T x m i = some en → en.abort = false → ∀ f y ρ, en.wk f y ρ → y.Θ.OK) :
    ∀ n, n ≤ N → ∀ x : KW, x.Θ.OK → ∀ ls e ρ,
      erwpK (ℍ := ℍ) KW.PostK (fun x => x.Θ.view x.c) (fun z => opTableK z.lo (T z)) Qin x n ls
        e ρ →
      erwpK (ℍ := ℍ) KW.PostK (fun x => x.Θ.view x.c) (fun z => opTableK z.lo OpTabK.empty) Qout
        x n ls (hndE (hndVal n₀ qs hr hs) e) ρ :=
  erwpK_handle_sched (fun _ _ _ h₁ h₂ => h₁.trans h₂) KW.postK_refl (Inv := fun x => x.Θ.OK)
    (fun x hx => LocTy.view_down hx.1 x.c) (fun _ _ h => by rw [h])
    (fun _ _ h => tabLe_postK (fun z : KW => opTableK z.lo OpTabK.empty) h) hS hwk hOK

/-! ### At one world -/

/-- `KapRelN` at any table is `KapRelK` at one world, at any floor (`kapRelK_lift_iff` at the
table `opTableN T`). -/
theorem kapRelK_liftT_iff (lo : Life) (Φ : LocFam) (T : OpTabN) (Q : PostN) (en : OpEntN)
    (Tc : Option OpTabN) (k : Nat) (ls : List SRec) (κ : Val) (ρ : WRes) :
    KapRelK (ℍ := ℍ) (fun _ _ => True) (fun _ => Φ) (fun _ => lo)
        (fun _ => opTableK lo (liftTabK T)) (fun _ => Q) (liftEntK en) lo
        (Tc.map (fun T _ => liftTabK T)) k ls κ ρ ↔
      KapRelN (ℍ := ℍ) Φ (opTableN T) Q en Tc k ls κ ρ := by
  constructor
  · rintro ⟨hu, f, -, h⟩
    refine ⟨hu, fun ls' he k' hk' => ⟨fun w σ₁ σ₂ hB hc => ?_, fun hq Tk hTk => ?_⟩⟩
    · have := (h () trivial ls' he k' hk').1 w σ₁ σ₂ hB hc
      rw [erwp_opTableN_eq_erwpK lo]; exact this
    · have := (h () trivial ls' he k' hk').2 hq (fun _ => liftTabK Tk) (by rw [hTk]; rfl)
      rw [erwp_opTableN_eq_erwpK lo]; exact this
  · rintro ⟨hu, h⟩
    refine ⟨hu, lo, le_rfl, fun _ _ ls' he k' hk' => ⟨fun w σ₁ σ₂ hB hc => ?_,
      fun hq Tk hTk => ?_⟩⟩
    · have := (h ls' he k' hk').1 w σ₁ σ₂ hB hc
      rw [erwp_opTableN_eq_erwpK lo] at this; exact this
    · cases Tc with
      | none => cases hTk
      | some T₀ =>
          cases Option.some.inj hTk
          have := (h ls' he k' hk').2 hq T₀ rfl
          rw [erwp_opTableN_eq_erwpK lo] at this; exact this

/-- `erwp_handle_le` from `erwpK_handle_le`. -/
theorem erwp_handle_le_of_K {Φ : LocFam} (hΦ : Φ.Down) (N : Nat) (Tin Tout : OpTabN)
    (hTinD : Tin.Down) (hTout : Tout.Down) (n₀ : UInt32) (hTin : ∀ m i, m ≠ n₀ → Tin m i = Tout m i)
    (qs hr hs : Val) (Qin Qout : PostN) (hQout : Qout.Down)
    (hq : ∀ i en, Tin n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag)
    (Tc : UInt32 → Option OpTabN)
    (hTc : ∀ i en, Tin n₀ i = some en → en.abort = false → en.q ≠ .lin → ∀ Tk, Tc i = some Tk →
      ∃ T₁, en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁) ∧ T₁.Sub Tk ∧ Tk.Down)
    (hret : ∀ k, k ≤ N → ∀ ls v ρ, Qin k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val hr) (.val v)) ρ)
    (hop : ∀ i en, Tin n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ k, k ≤ N → ∀ ls v (κ : Val) ρ,
        (en.PA k ls v ⋆ KapRelN (ℍ := ℍ) Φ (opTableN Tout) Qout en (Tc i) k ls κ) ρ →
        erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val c) (.pair (.val v) κ.1)) ρ) ∧
      (en.abort = true → ∀ k, k ≤ N → ∀ ls v ρ, en.PA k ls v ρ →
        erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val c) (.val v)) ρ)) :
    ∀ n, n ≤ N → ∀ ls e ρ, erwp (ℍ := ℍ) Φ (opTableN Tin) Qin n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout n ls (hndE (hndVal n₀ qs hr hs) e) ρ := by
  intro n hnN ls e ρ h
  rw [erwp_opTableN_eq_erwpK 0] at h ⊢
  refine erwpK_handle_le (ℍ := ℍ) (V := fun _ _ => True) (fun _ _ _ _ _ => trivial)
    (Φ := fun _ => Φ) (Inv := fun _ => True) (fun _ _ => hΦ) (fun _ _ _ => rfl) (fl := fun _ => 0) N
    (fun _ => liftTabK Tin) (fun _ => liftTabK Tout) (fun _ => hTinD.liftK)
    (fun _ => hTout.liftK) (fun _ _ _ _ _ _ _ _ h => h) n₀ ?_ qs hr hs (fun _ => Qin)
    (fun _ => Qout) (fun _ => hQout) ?_ ?_ ?_ (fun i => (Tc i).map (fun T _ => liftTabK T)) ?_
    (fun _ => trivial) (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) ?_ ?_ n hnN () trivial ls e ρ h
  · intro _ m i hm
    simp only [liftTabK, hTin m i hm]
  · intro _ i en h₁ ha
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hq i en₀ h₀ ha
  · intro _ m i en h₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hTinD.wcl m i en₀ h₀
  · intro _ i en h₁ _ _ _ _ _ _ _ _ _
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    trivial
  · intro _ i en h₁ ha hq' Tk hTk
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    cases hTc' : Tc i with
    | none => rw [hTc'] at hTk; cases hTk
    | some T₀ =>
        rw [hTc'] at hTk
        cases Option.some.inj hTk
        obtain ⟨T₁, hf, hsub, hTkD⟩ := hTc i en₀ h₀ ha hq' T₀ hTc'
        refine ⟨fun _ => liftTabK T₁, ?_, fun _ m j e he => ?_, fun _ => hTkD.liftK⟩
        · simp only [liftEntK, hf, Option.map_some]
          rw [cancelOblN_eq_K 0 Φ T₁]
        · obtain ⟨e₀, he₀, rfl⟩ := liftTabK_some he
          exact liftTabK_of_some (hsub m j e₀ he₀)
  · intro _ k hk ls' v ρ' hv
    have h' := hret k hk ls' v ρ' hv
    rw [erwp_opTableN_eq_erwpK 0] at h'
    exact h'
  · intro _ i en h₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    obtain ⟨c, hc, h₁, h₂⟩ := hop i en₀ h₀
    refine ⟨c, hc, fun ha k hk ls' v κ ρ' hp => ?_, fun ha k hk ls' v ρ' hp => ?_⟩
    · obtain ⟨ρa, ρk, hcak, hA, hK⟩ := hp
      have := h₁ ha k hk ls' v κ ρ' ⟨ρa, ρk, hcak, hA,
        (kapRelK_liftT_iff 0 Φ Tout Qout en₀ (Tc i) k ls' κ ρk).mp hK⟩
      rw [erwp_opTableN_eq_erwpK 0] at this; exact this
    · have := h₂ ha k hk ls' v ρ' hp
      rw [erwp_opTableN_eq_erwpK 0] at this; exact this

/-- `erwp_handleLe` from `erwpK_handleLe_le`. -/
theorem erwp_handleLe_of_K {Φ : LocFam} (hΦ : Φ.Down) (Tin Tout : OpTabN)
    (hTinD : Tin.Down) (hTout : Tout.Down) (n₀ : UInt32) (hTin : ∀ m i, m ≠ n₀ → Tin m i = Tout m i)
    (qs hr hs : Val) (Qin Qout : PostN) (hQout : Qout.Down)
    (hq : ∀ i en, Tin n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag)
    (Tc : UInt32 → Option OpTabN)
    (hTc : ∀ i en, Tin n₀ i = some en → en.abort = false → en.q ≠ .lin → ∀ Tk, Tc i = some Tk →
      ∃ T₁, en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁) ∧ T₁.Le Tk ∧ Tk.Down)
    (hret : ∀ k ls v ρ, Qin k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val hr) (.val v)) ρ)
    (hop : ∀ i en, Tin n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ k ls v (κ : Val) ρ,
        (en.PA k ls v ⋆ KapRelN (ℍ := ℍ) Φ (opTableN Tout) Qout en (Tc i) k ls κ) ρ →
        erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val c) (.pair (.val v) κ.1)) ρ) ∧
      (en.abort = true → ∀ k ls v ρ, en.PA k ls v ρ →
        erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val c) (.val v)) ρ)) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN Tin) Qin n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout n ls (hndE (hndVal n₀ qs hr hs) e) ρ := by
  intro n ls e ρ h
  rw [erwp_opTableN_eq_erwpK 0] at h ⊢
  refine erwpK_handleLe_le (ℍ := ℍ) (V := fun _ _ => True) (fun _ _ _ _ _ => trivial)
    (Φ := fun _ => Φ) (Inv := fun _ => True) (fun _ _ => hΦ) (fun _ _ _ => rfl) (fl := fun _ => 0) n
    (fun _ => liftTabK Tin) (fun _ => liftTabK Tout) (fun _ => hTinD.liftK)
    (fun _ => hTout.liftK) (fun _ _ _ _ _ _ _ _ h => h) n₀ ?_ qs hr hs (fun _ => Qin)
    (fun _ => Qout) (fun _ => hQout) ?_ ?_ ?_ (fun i => (Tc i).map (fun T _ => liftTabK T)) ?_
    (fun _ => trivial) (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) ?_ ?_ n le_rfl () trivial ls e ρ h
  · intro _ m i hm
    simp only [liftTabK, hTin m i hm]
  · intro _ i en h₁ ha
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hq i en₀ h₀ ha
  · intro _ m i en h₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hTinD.wcl m i en₀ h₀
  · intro _ i en h₁ _ _ _ _ _ _ _ _ _
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    trivial
  · intro _ i en h₁ ha hq' Tk hTk
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    cases hTc' : Tc i with
    | none => rw [hTc'] at hTk; cases hTk
    | some T₀ =>
        rw [hTc'] at hTk
        cases Option.some.inj hTk
        obtain ⟨T₁, hf, hsub, hTkD⟩ := hTc i en₀ h₀ ha hq' T₀ hTc'
        refine ⟨fun _ => liftTabK T₁, ?_, fun _ => hsub.liftK, fun _ => hTkD.liftK⟩
        simp only [liftEntK, hf, Option.map_some]
        rw [cancelOblN_eq_K 0 Φ T₁]
  · intro _ k _ ls' v ρ' hv
    have h' := hret k ls' v ρ' hv
    rw [erwp_opTableN_eq_erwpK 0] at h'
    exact h'
  · intro _ i en h₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    obtain ⟨c, hc, h₁, h₂⟩ := hop i en₀ h₀
    refine ⟨c, hc, fun ha k _ ls' v κ ρ' hp => ?_, fun ha k _ ls' v ρ' hp => ?_⟩
    · obtain ⟨ρa, ρk, hcak, hA, hK⟩ := hp
      have := h₁ ha k ls' v κ ρ' ⟨ρa, ρk, hcak, hA,
        (kapRelK_liftT_iff 0 Φ Tout Qout en₀ (Tc i) k ls' κ ρk).mp hK⟩
      rw [erwp_opTableN_eq_erwpK 0] at this; exact this
    · have := h₂ ha k ls' v ρ' hp
      rw [erwp_opTableN_eq_erwpK 0] at this; exact this

/-- `erwp_ccatchLe` from `erwpK_ccatchLe`. -/
theorem erwp_ccatchLe_of_K {Φ : LocFam} (hΦ : Φ.Down) {T Tout : OpTabN} (hT : T.Le Tout)
    (hToutD : Tout.Down) :
    ∀ n ls e ρ, cancelOblN (ℍ := ℍ) Φ T n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) unitPost n ls (ccatchE e) ρ := by
  intro n ls e ρ h
  rw [cancelOblN, erwp_eq_erwpK_of (cancelTabK_lift 0 T) Φ _] at h
  rw [erwp_opTableN_eq_erwpK 0]
  exact erwpK_ccatchLe (ℍ := ℍ) (V := fun _ _ => True) (fun _ => trivial) (Φ := fun _ => Φ)
    (Inv := fun _ => True) (fun _ _ => hΦ) (fl := fun _ => 0) (T := fun _ => liftTabK T)
    (Tout := fun _ => liftTabK Tout) (fun _ => hT.liftK) (fun _ => hToutD.liftK)
    (fun _ _ _ _ _ _ _ _ _ _ => trivial) n () trivial ls e ρ h

/-- `erwp_handle` from `erwpK_handle`. -/
theorem erwp_handle_of_K {Φ : LocFam} (hΦ : Φ.Down) (Tin Tout : OpTabN) (hTinD : Tin.Down)
    (hTout : Tout.Down) (n₀ : UInt32) (hTin : ∀ m i, m ≠ n₀ → Tin m i = Tout m i) (qs hr hs : Val)
    (Qin Qout : PostN) (hQout : Qout.Down)
    (hq : ∀ i en, Tin n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag)
    (Tc : UInt32 → Option OpTabN)
    (hTc : ∀ i en, Tin n₀ i = some en → en.abort = false → en.q ≠ .lin → ∀ Tk, Tc i = some Tk →
      ∃ T₁, en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁) ∧ T₁.Sub Tk ∧ Tk.Down)
    (hret : ∀ k ls v ρ, Qin k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val hr) (.val v)) ρ)
    (hop : ∀ i en, Tin n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ k ls v (κ : Val) ρ,
        (en.PA k ls v ⋆ KapRelN (ℍ := ℍ) Φ (opTableN Tout) Qout en (Tc i) k ls κ) ρ →
        erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val c) (.pair (.val v) κ.1)) ρ) ∧
      (en.abort = true → ∀ k ls v ρ, en.PA k ls v ρ →
        erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val c) (.val v)) ρ)) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN Tin) Qin n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout n ls (hndE (hndVal n₀ qs hr hs) e) ρ :=
  fun n => erwp_handle_le_of_K hΦ n Tin Tout hTinD hTout n₀ hTin qs hr hs Qin Qout hQout hq Tc
    hTc (fun k _ => hret k)
    (fun i en hT => by
      obtain ⟨c, hc, h₁, h₂⟩ := hop i en hT
      exact ⟨c, hc, fun ha k _ => h₁ ha k, fun ha k _ => h₂ ha k⟩) n le_rfl

end BoCa.Fig16.LogRel.Core.Chain.SI

end
