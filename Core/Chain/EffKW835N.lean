import Core.Chain.FamKW835N
import Core.Chain.MechK835N2

/-!
# `[sub]`, `[perform]` and `[raise]` at the typed world  `[spec §19, §27]`

Core's `sub_compatC`, `perform_compatC` and `raise_compatC` (`Core/EffFin.lean`) at `SemJN`, step
for step, over `Eff835N`'s helpers, `F_Σ R` read at the row's table through
`cN_effOf_tabF` (`tabF (rdN δ) ()`):

* **E3**: the table grows with the row (`tabF_le_of_rowLe`, by `entF_le_of_leF` and `finF_mono`),
  so a run at the smaller row's table is one at the larger's (`opTableK_le`, `erwpK_mono`);
* **E5**: a computation that never stops, framed, in front of an `erwpK` at any table
  (`erwpK_bind_pure_frame`: `rwp_frame`, `erwpK_bindR`);
* **E6**: a `perform` stops at once (`erwpK_perform_here`); the cancel run of the empty region is in
  every cancel obligation of a row's entry (`entN_start`, `cancelK_start`), at every world;
* **E7**: a `raise` stops at once, at an argument owning nothing (`erwpK_raise_here`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont performE raiseE cancelVal opPayload)

variable {ι M : Type}

/-- **A pure prefix in front of an `erwpK`, framing `R` through its run**
(`erwp_bind_pure_frame`): a run that never stops (`rwp`), the frame carried by `rwp_frame`, then
the context at any table (`erwpK_bindR`). -/
theorem erwpK_bind_pure_frame {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι}
    (hL : ∀ x, (Tb x).Local) {x : ι} (hΦ : (Φ x).Down) (K : Kont) (e : Expr) (ls : List SRec)
    (P : PostN) (R : List SRec → WProp) {Q : ι → PostN}
    (hR : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ ρ, R ls ρ → R ls' ρ)
    (h : ∀ k ls' (v : Val) ρ, (P k ls' v ⋆ R ls') ρ →
      erwpK (ℍ := ℍ) V Φ Tb Q x k ls' (K.plug v.1) ρ)
    {n : Nat} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (hw : rwp (ℍ := ℍ) (Φ x) P n ls e ρ₁)
    (hR₂ : R ls ρ₂) : erwpK (ℍ := ℍ) V Φ Tb Q x n ls (K.plug e) ρ :=
  erwpK_bindR hL hΦ K (rwp_mono (fun k ls' v ρ hp => h k ls' v ρ hp) (rwp_frame R hR hc hw hR₂))

/-- **A plain frame around an effectful computation at `erwpK`, read at the worlds `Inv` holds
at** (`erwpK_frame_plain`): the run starts at such a world, the post order keeps `Inv`, and every
world an entry owes at is one. -/
theorem erwpK_frame_plainI {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    {Φ : ι → LocFam} {Inv : ι → Prop} (hΦ : ∀ x, Inv x → (Φ x).Down)
    (hΦV : ∀ x y, V x y → Φ y = Φ x) (hVI : ∀ x y, V x y → Inv x → Inv y) {fl : ι → Life}
    {T : ι → OpTabK ι} (hTV : ∀ x y, V x y → (opTableK (fl y) (T y)).Le (opTableK (fl x) (T x)))
    (K : Kont) (hH : ∀ n, K.HasHnd n = false) (hC : ∀ n, K.Catches n = false)
    (Fr : ι → List SRec → WProp)
    (hFs : ∀ x ls ls', (∀ a, a ∈ ls' ↔ a ∈ ls) → ∀ ρ, Fr x ls ρ → Fr x ls' ρ)
    (hFV : ∀ x y, V x y → ∀ ls ρ, Fr x ls ρ → Fr y ls ρ)
    (hwkI : ∀ x n i en, T x n i = some en → ∀ f y ρ, en.wk f y ρ → Inv y)
    (hwl : ∀ x n i en, T x n i = some en → ∀ ls ls' ρ σ ρ', ResU.CompS ρ σ ρ' →
      en.wc ls ls' ρ' → en.wc ls ls' ρ)
    (hkl : ∀ x n i en, T x n i = some en → ∀ f y ρ σ ρ', ResU.CompS ρ σ ρ' → ResU.Valid ρ' →
      en.wk f y ρ' → en.wk f y ρ)
    (hFe : ∀ x n i en, T x n i = some en → ∀ ls ls' ρ σ ρ', ResU.CompS ρ σ ρ' →
      en.wc ls ls' ρ' → Fr x ls σ → Fr x ls' σ)
    (hFk : ∀ x n i en, T x n i = some en → ∀ f y ls ρ σ ρ', ResU.CompS ρ σ ρ' →
      ResU.Valid ρ' → en.wk f y ρ' → Fr x ls σ → Fr y ls σ)
    (hW : ∀ x n i en, T x n i = some en → en.abort = true → ∀ ls ρ, Fr x ls ρ → NoOwn ρ)
    (hU : ∀ x n i en, T x n i = some en → en.q = .unr → ∀ ls ρ, Fr x ls ρ → ρ = PMap.empty)
    (hK : ∀ x n i en, T x n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ y k ls K₁ ρ σ ρ', cancelOKK en y k ls K₁ ρ → Fr y ls σ → ResU.CompS ρ σ ρ' →
        cancelOKK en y k ls (K.comp K₁) ρ')
    (Q₁ Q : ι → PostN)
    (hkv : ∀ y, Inv y → ∀ k ls (v : Val) ρ, (Q₁ y k ls v ⋆ Fr y ls) ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q y k ls (K.plug v.1) ρ) :
    ∀ n x, Inv x → ∀ ls e ρ, erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q₁ x n ls e ρ →
      ∀ ρ₂ ρ', Fr x ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q x n ls (K.plug e) ρ' := by
  have hL : ∀ z, (opTableK (fl z) (T z)).Local := fun z => opTableK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx ls e ρ h ρ₂ ρ' hF hc
  rw [erwpK_eq] at h ⊢
  refine rwpG_bind (hΦ x hx) K ?_
  refine rwpG_mono_le (fun k hk ls' t σ ⟨⟨σ₁, σ₂, hcσ, hp, hF'⟩, hvσ⟩ => ?_)
    (rwpG_validK (rwpG_frame (Fr x) (hFs x) hc h hF))
  rcases hp with ⟨v, rfl, y, hy, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact erwpK_shift hVt hΦV hTV hL hy hk
      (hkv y (hVI x y hy hx) k ls' v σ ⟨σ₁, σ₂, hcσ, hv, hFV x y hy ls' σ₂ hF'⟩)
  · -- a `perform`: the frame joins the continuation's share
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcσ
    have hvk : ResU.Valid ρk' := (ResU.Valid.split hcσ' hvσ).2
    have hKo : (K.comp K₁).HasHnd m = false := by rw [hasHnd_comp, hH, hK₁]; rfl
    have ht' : K.plug (K₁.plug (performE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨K.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩ ⟨ρa, ρk', hcσ', hA,
        fun hq => ?_, f, hf, fun y hy ls'' he => ⟨fun k' hk'' w τ₁ τ₂ hB hcτ => ?_,
          fun hq P hP => ?_⟩⟩⟩))
    · rw [hu hq, hU x m i en hT hq ls' σ₂ hF'] at hk'
      exact eq_of_compS_empty_left hk'
    · have hyk := hkl x m i en hT f y ρk σ₂ ρk' hk' hvk hy
      have hFy := hFk x m i en hT f y ls'' ρk σ₂ ρk' hk' hvk hy
        (hFe x m i en hT ls' ls'' ρk σ₂ ρk' hk' he hF')
      obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ
      have h₁ := (hcont y hyk ls'' (hwl x m i en hT ls' ls'' ρk σ₂ ρk' hk' he)).1 k' hk'' w τ₁ z
        hB hz
      simp only [erwpCK, show k' < n by omega, if_true] at h₁ ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) y (hwkI x m i en hT f y ρk hyk) ls'' _ z h₁ σ₂ τ₂ hFy hcz
    · have hyk := hkl x m i en hT f y ρk σ₂ ρk' hk' hvk hy
      have hFy := hFk x m i en hT f y ls'' ρk σ₂ ρk' hk' hvk hy
        (hFe x m i en hT ls' ls'' ρk σ₂ ρk' hk' he hF')
      exact hK x m i en hT ha hq y k ls'' K₁ ρk σ₂ ρk'
        (fun P hP => (hcont y hyk ls'' (hwl x m i en hT ls' ls'' ρk σ₂ ρk' hk' he)).2 hq P hP)
        hFy hk' P hP
  · -- a `raise`: the frame is left behind
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hn⟩ := pure_sep_iff.mp hp
    obtain ⟨ρn', hn', hcσ'⟩ := compS_reassoc hcan hcσ
    have hKo : (K.comp K₁).Catches m = false := by rw [catches_comp, hC, hK₁]; rfl
    have ht' : K.plug (K₁.plug (raiseE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE true (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    exact rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
      ⟨K.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩ ⟨ρa, ρn', hcσ', ⟨hPA, hnA⟩,
        noOwn_compS hn' hn (hW x m i en hT ha ls' σ₂ hF')⟩⟩))

/-- **A `raise` stops at once, at an argument that holds nothing owned** (`erwp_raise_here`): an
abortive stop owes no continuation, so it reads no world. -/
theorem erwpK_raise_here {V : ι → ι → Prop} {Φ : ι → LocFam} {fl : ι → Life} {T : ι → OpTabK ι}
    {x : ι} {n i : UInt32} {en : OpEntK ι} (hT : T x n i = some en) (ha : en.abort = true)
    {Q : ι → PostN} {k : Nat} {ls : List SRec} {v : Val} {ρ : WRes} (h : en.PA k ls v ρ)
    (hn : NoOwn ρ) :
    erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q x k ls
      (raiseE (.val (opPayload n i v))) ρ := by
  rw [erwpK_eq]
  exact rwpG_here (final_opPlug (K := .hole) (r := true) (payloadName_opPayload n i v)
    (by simp [OpFree, Kont.Catches])) (Or.inr (Or.inr
      ⟨.hole, n, i, v, en, pure_sep_mk ⟨rfl, rfl, hT, ha⟩
        ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, ⟨h, hn⟩, noOwn_empty⟩⟩))

/-- **The cancel run of the empty region** (`cancelOblN_start`), at every world: it ends at once,
keeping no error. -/
theorem cancelK_start {V : ι → ι → Prop} {Φ : ι → LocFam} {fl : ι → Life} (T : ι → OpTabK ι)
    (y : ι) (k : Nat) (ls : List SRec) :
    erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T z)) (fun _ _ _ _ _ => False) y k ls
      (raiseE (.val (cancelVal none))) PMap.empty := by
  rw [erwpK_eq]
  exact rwpG_here (final_opPlug (K := .hole) (r := true) (payloadName_cancelVal none)
    (by simp [OpFree, Kont.Catches])) (Or.inr (Or.inr ⟨.hole, none, pure_sep_mk ⟨rfl, rfl⟩
      ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, trivial⟩, noOwn_empty⟩⟩))

/-- **E3 over a world index: the table grows with the row** (Core's
`effWp_sub`'s table step), at every answer type and world. -/
theorem tabF_le_of_rowLe (R : RowRd ι M) {S S' : Row} (hle : RowLe S S') (μ : M) (Rt Rt' : VTy)
    (x : ι) : (tabF (ℍ := ℍ) R μ (CTy.effOf S Rt) x).Le (tabF (ℍ := ℍ) R μ (CTy.effOf S' Rt') x) := by
  intro n i en hT
  obtain ⟨o, hf, rfl⟩ := tabF_effOf_some_find hT
  obtain ⟨o', hf', hs, hfl⟩ := hle n i o hf
  exact ⟨_, by rw [tabF_effOf_find, hf']; rfl, entF_le_of_leF R hs fun hcap =>
    finF_mono R (R.sub μ n) o.fin (hfl (by simp [OpSig.finRead, hcap]))⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont performE raiseE cancelVal opPayload)

/-- **`F_Σ` grows with the row** (`erwp_rowLe`, Core's `effWp_sub`): at every floor, every stop
of the smaller row's table is one of the larger's. -/
theorem erwp_rowLe {S S' : Row} (hle : RowLe S S') {A : VTy} {δ : LSub} {Θ : LocTy}
    {c : Loc → Option Life} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : cN (ℍ := ℍ) (CTy.effOf S A) δ Θ c n ls e ρ) : cN (ℍ := ℍ) (CTy.effOf S' A) δ Θ c n ls e ρ := by
  rw [cN_effOf_tabF] at h ⊢
  intro lo
  exact erwpK_mono (Tb' := fun z : KW => opTableK z.lo
      (tabF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () (CTy.effOf S' A) z)) (fun _ _ h => h) (fun _ _ _ _ _ h => h)
    (fun z k ls t Ψ Ψ' ρ hΨ hh =>
      opTableK_le (tabF_le_of_rowLe _ hle () A A z) k ls t Ψ Ψ' ρ hΨ hh) n _ ls e ρ (h lo)

/-- **E6: an entry's cancel obligation holds of the empty region** (`entN_start`, Core's
`ent_start`), at every world the stop resumes at. -/
theorem entN_start (δ : LSub) (o : OpSig) (x y : KW) (k : Nat) (ls : List SRec) :
    cancelOKK ((rdN (ℍ := ℍ) δ).ent () o.n o.q o.A o.B (finF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () o.fin) x)
      y k ls .hole PMap.empty := by
  intro P hP
  simp only [RowRd.ent] at hP
  split at hP
  · rw [finF_eq_ite] at hP
    split at hP
    · cases hP
    · cases hP; exact cancelK_start _ y k ls
  · cases hP

/-- **`[sub]`** (Core's `sub_compatC`): a row may grow, its entries' cancel rows with it. -/
theorem sub_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {S S' : Row} {A : VTy}
    (hle : RowLe S S') (h : SemJN (ℍ := ℍ) Δ Γ e (.comp (CTy.effOf S A))) :
    SemJN (ℍ := ℍ) Δ Γ e (.comp (CTy.effOf S' A)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  exact erwp_rowLe hle (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg)

/-- **`[perform]`**, at any cancel row (Core's `perform_compatC`): the argument's run never
stops, and the operation stops at once at its entry, at the floor the run is read at; its answer
is read at the world the stop resumes at. -/
theorem perform_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {S : Row} {o : OpSig}
    (hf : Row.find S o.n o.i = some o) (hna : o.abort = false)
    (h : SemJN (ℍ := ℍ) Δ Γ V (.val o.A)) :
    SemJN (ℍ := ℍ) Δ Γ (performE (opArgE o.n o.i V)) (.comp (CTy.effOf S o.B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine (cN_effOf_tabF S o.B δ Θ c n ls _ ρ).mpr fun lo => ?_
  change erwpK (ℍ := ℍ) _ _ _ _ _ n ls ((Kont.appR (.val (.prim .perform))
    (.pairR (Val.i32 o.n) (.pairR (Val.i32 o.i) .hole))).plug (substAll γ V)) ρ
  refine erwpK_bind_pure_frame (x := (⟨Θ, c, lo⟩ : KW)) (Φ := fun z : KW => z.Θ.view z.c)
    (fun _ => opTableK_local _ _) (LocTy.view_down hΘ.1 c) _ _ ls
    (fun k _ v ρ => vN (ℍ := ℍ) o.A δ Θ k v ρ) (fun _ => BoLo.emp) (fun _ _ _ _ h => h) ?_
    (ResU.comp_empty_right ρ)
    (rwp_of_erwp_empty (erwp_of_cN_ret (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg))) ⟨rfl, trivial⟩
  rintro k ls' v σ ⟨σ₁, σ₂, hc', hv, rfl, -⟩
  rw [ResU.CompS.functional hc' (ResU.comp_empty_right σ₁)]
  have hT : tabF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () (CTy.effOf S o.B) ⟨Θ, c, lo⟩ o.n o.i =
      some ((rdN (ℍ := ℍ) δ).ent () o.n o.q o.A o.B (finF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () o.fin)
        ⟨Θ, c, lo⟩) := by
    rw [tabF_effOf_find, hf]; rfl
  exact erwpK_perform_here (fun y => KW.postK_refl y) hT
    (by simpa [RowRd.ent, OpSig.abort] using hna) lo le_rfl
    (fun y _ k ls => entN_start δ o _ y k ls) (fun _ _ _ _ _ _ hB => hB.1) hv

/-- **`[raise]`**: an abortive operation, at any answer type, its argument owning nothing (Core's
`raise_compatC`). -/
theorem raise_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {S : Row} {o : OpSig} {B : VTy}
    (hf : Row.find S o.n o.i = some o) (ha : o.abort = true)
    (hd : ∀ δ Θ n v ρ, vN (ℍ := ℍ) o.A δ Θ n v ρ → NoOwn ρ)
    (h : SemJN (ℍ := ℍ) Δ Γ V (.val o.A)) :
    SemJN (ℍ := ℍ) Δ Γ (raiseE (opArgE o.n o.i V)) (.comp (CTy.effOf S B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine (cN_effOf_tabF S B δ Θ c n ls _ ρ).mpr fun lo => ?_
  change erwpK (ℍ := ℍ) _ _ _ _ _ n ls ((Kont.appR (.val (.prim .raise))
    (.pairR (Val.i32 o.n) (.pairR (Val.i32 o.i) .hole))).plug (substAll γ V)) ρ
  refine erwpK_bind_pure_frame (x := (⟨Θ, c, lo⟩ : KW)) (Φ := fun z : KW => z.Θ.view z.c)
    (fun _ => opTableK_local _ _) (LocTy.view_down hΘ.1 c) _ _ ls
    (fun k _ v ρ => vN (ℍ := ℍ) o.A δ Θ k v ρ) (fun _ => BoLo.emp) (fun _ _ _ _ h => h) ?_
    (ResU.comp_empty_right ρ)
    (rwp_of_erwp_empty (erwp_of_cN_ret (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg))) ⟨rfl, trivial⟩
  rintro k ls' v σ ⟨σ₁, σ₂, hc', hv, rfl, -⟩
  rw [ResU.CompS.functional hc' (ResU.comp_empty_right σ₁)]
  have hT : tabF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () (CTy.effOf S B) ⟨Θ, c, lo⟩ o.n o.i =
      some ((rdN (ℍ := ℍ) δ).ent () o.n o.q o.A o.B (finF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () o.fin)
        ⟨Θ, c, lo⟩) := by
    rw [tabF_effOf_find, hf]; rfl
  exact erwpK_raise_here hT (by simpa [RowRd.ent, OpSig.abort] using ha) hv (hd _ _ _ _ _ hv)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
