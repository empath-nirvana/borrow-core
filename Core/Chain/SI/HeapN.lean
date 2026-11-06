import Core.Chain.SI.WpN
import Core.EffMachine

/-!
# The heap rules (`[TR]` 6.141–6.145) at the step index

Each heap operation is one head step to a value. `rwp_head1` reads such a term at `rwp`: the run
of no step must be able to step, and the run of one step ends at a value, where the
post-configuration is asked at `n − 1`. The runs of more steps do not exist, since a value does
not step.

The rules are `wpTS_alloc`, `wpTS_free`, `wpTS_load`, `wpTS_load_I` and `wpTS_store`, with the
post-configuration as printed. Two things differ from `wpTS`: an allocation's run is any step,
at any location the memory does not hold (`wpTS` picks one by its allocator), and the update
`ρ ↭ π` is the printed one read at the index (`updVN_of_updV`: the printed `mut` clause fixes
`P̂`, so `PredStep` holds by equality).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont freeE hndE ubindE ccatchE cfinE)

/-! ### The printed `↭` at the index -/

/-- The printed `↭` is `↭` at every index: the printed `mut` clause keeps `β` and `P̂`. -/
theorem updN_of_upd (Φ : LocFam) (n : Nat) {ρ₁ ρ₂ : WRes} (h : ResU.Upd ρ₁ ρ₂) :
    UpdN Φ n ρ₁ ρ₂ := by
  refine ⟨h.1, fun l ψ hg hk => ?_, fun l ψ hg hk => ?_⟩
  · rcases CellU.rep ψ with ⟨u, rfl⟩ | ⟨s, u, τ, m, rfl⟩ | ⟨c, u, τ, m, Q, k, rfl⟩
    · simp at hk
    · simp at hk
    · obtain ⟨v', χ', hh', hw', h'⟩ := (h.2 l c Q).mp ⟨u, τ, m, k, hg⟩
      have e : cellPred (CellU.mutOf c u τ m Q k) = cellPred (CellU.mutOf c v' χ' hh' Q hw') := by
        funext w r
        exact propext ((mpred_mutOf w r).trans (mpred_mutOf w r).symm)
      exact ⟨_, h', rfl, rfl, rfl, fun _ => e, fun _ _ _ w r hp => .inl (e ▸ hp)⟩
  · rcases CellU.rep ψ with ⟨u, rfl⟩ | ⟨s, u, τ, m, rfl⟩ | ⟨c, u, τ, m, Q, k, rfl⟩
    · simp at hk
    · simp at hk
    · obtain ⟨v', χ', hh', hw', h'⟩ := (h.2 l c Q).mpr ⟨u, τ, m, k, hg⟩
      have e : cellPred (CellU.mutOf c v' χ' hh' Q hw') = cellPred (CellU.mutOf c u τ m Q k) := by
        funext w r
        exact propext ((mpred_mutOf w r).trans (mpred_mutOf w r).symm)
      exact ⟨_, h', rfl, rfl, rfl, fun _ => e, fun _ _ _ w r hp => .inl (e ▸ hp)⟩

theorem updVN_of_updV (Φ : LocFam) (n : Nat) {ρ₁ ρ₂ : WRes} (h : ResU.UpdV ρ₁ ρ₂) :
    UpdVN Φ n ρ₁ ρ₂ :=
  ⟨updN_of_upd Φ n h.1, h.2⟩

/-! ### One head step to a value -/

/-- A step of a head redex is a head step at the hole. -/
theorem step1_head {μ₀ μ₀' : Heap} {a a₀ : Expr} (hred : Head (ℍ := ℍ) μ₀ a μ₀' a₀)
    {μ μ₁ : Heap} {e₁ : Expr} (h : Step1 (ℍ := ℍ) μ a μ₁ e₁) : Head (ℍ := ℍ) μ a μ₁ e₁ := by
  obtain ⟨K', b, b', he, rfl, hb⟩ := h
  obtain ⟨rfl, rfl⟩ := plug_decomp hb Kont.hole K' hred (by simpa [Kont.plug] using he)
  simpa [Kont.plug] using hb

/-- **One head step to a value, at `rwp`.** -/
theorem rwp_head1 {Φ : LocFam} {Q : PostN} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    {μ₀ μ₀' : Heap} {a₀ : Expr} (hred : Head (ℍ := ℍ) μ₀ e μ₀' a₀)
    (hstep : ∀ (ρf fρ : WRes) (ps : List FrameRec) (μ : Heap),
      ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → TWNC fρ ps (rsOf ls) → Tagged fρ ps ls →
      ResU.Lower fρ μ → FinDom μ →
      (∃ μ₁ e₁, Head (ℍ := ℍ) μ e μ₁ e₁) ∧
      ∀ μ₁ e₁, Head (ℍ := ℍ) μ e μ₁ e₁ →
        ∃ v : Val, e₁ = v.1 ∧ EndOK Φ Q (n - 1) ls ρ ρf ps μ₁ v) :
    rwp (ℍ := ℍ) Φ Q n ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun
  obtain ⟨⟨μ₁, e₁, hh⟩, hend⟩ := hstep ρf fρ ps μ hf hc hT htg hl hfd
  have hnv : ¬ IsVal e := hred.not_isVal
  cases hrun with
  | refl =>
      exact ⟨fun v hv => absurd (hv ▸ v.2) hnv,
        fun _ => ⟨μ₁, e₁, ⟨Kont.hole, e, e₁, by simp [Kont.plug], by simp [Kont.plug], hh⟩⟩⟩
  | @more j' _ μ₂ _ _ e₂ _ h t =>
      obtain ⟨w, rfl, hEnd⟩ := hend μ₂ e₂ (step1_head hred h)
      cases t with
      | refl =>
          refine ⟨fun v hv => ?_, fun hn => absurd w.2 hn⟩
          have : v = w := Subtype.ext hv.symm
          subst this
          simpa using hEnd
      | more h' _ => exact absurd h' BoLo.no_step_val

/-! ### `[TR]` 6.141–6.145 -/

/-- **`[TR]` 6.141 (`wp-alloc`) at the step index**: `wpTS_alloc`, at every location the memory
does not hold. -/
theorem rwp_alloc {Φ : LocFam} (ls : List SRec) (v : Val) (Q : PostN) {n : Nat} {ρ : WRes}
    (h : (all fun l : BoCa.Loc => wand (ptoOwn l v) (Q (n - 1) ls (.loc l))) ρ) :
    rwp (ℍ := ℍ) Φ Q n ls (.app (.val (.prim .alloc)) (.val v)) ρ := by
  refine rwp_head1 (Head.alloc (fun _ => none) v 0 rfl) (fun ρf σ ps μ hf hσ hT htg hμ hfin => ?_)
  obtain ⟨τ, hτ, hval⟩ := id hμ
  obtain ⟨ℓ₀, hℓ₀⟩ := BoLo.finDom_block hfin
  refine ⟨⟨_, _, Head.alloc μ v ℓ₀ (by simpa using hℓ₀ 0)⟩, fun μ₁ e₁ hh => ?_⟩
  obtain ⟨l, hμl, rfl, rfl⟩ := head_alloc_inv hh
  have hl : τ.get l = none := (lower_eq_none_iff hval).mp hμl
  have hρl : ρ.get l = none :=
    ((ResU.Comp.eq_none_iff hσ l).mp (get_eq_none_of_flat hτ hl)).2
  obtain ⟨x, hx⟩ := (ResU.compS_defined_iff ρ (ResU.single l (CellU.ownOf v))).mpr
    (compatS_single_of_get_none hρl)
  obtain ⟨σ', hσ'x, hfx, hlow'⟩ := hash_compS_own hσ hμ hμl hx
  obtain ⟨y, hy, hyσ'⟩ := (ResU.CompS.assoc ρf ρ (ResU.single l (CellU.ownOf v)) σ').mp
    ⟨x, hx, hσ'x⟩
  cases ResU.CompS.functional hy hσ
  have hT' : TWNC σ' ps (rsOf ls) := TWNC.alloc hT hμ hμl hyσ' (hash_valid_comp hfx hσ'x)
  exact ⟨⟨.loc l, (Val.loc l).2⟩, rfl, x, PMap.empty, σ', σ', x, ps, ls,
    ResU.hash_symm hfx, hσ'x,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hfx hσ'x)),
    ResU.comp_empty_right σ', hlow', ResU.comp_empty_right x,
    updVN_of_updV Φ _ (updV_compS_own hx (hash_valid hf).2 (hash_valid hfx).2),
    noOwn_empty, hT', tagged_of_ag (fun a ha => alloc_ag hyσ' ha) htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, h l _ x rfl hx⟩

/-- **`[TR]` 6.142 (`wp-free`) at the step index** (`wpTS_free`). -/
theorem rwp_free {Φ : LocFam} (ls : List SRec) (l : BoCa.Loc) (v : Val) (Q : PostN) {n : Nat}
    {ρ : WRes} (h : (sep (ptoOwn l v) (Q (n - 1) ls v)) ρ) :
    rwp (ℍ := ℍ) Φ Q n ls (.app (.val (.prim .free)) (.val (.loc l))) ρ := by
  obtain ⟨ρ₁, ρ₂, hcρ, rfl, hQ⟩ := h
  refine rwp_head1 (Head.free (fun _ => some Val.unit) l Val.unit rfl)
    (fun ρf σ ps μ hf hσ hT htg hμ hfin => ?_)
  have h₂ : ResU.Hash ρf ρ₂ :=
    ResU.hash_symm (ResU.Hash.split hcρ (ResU.hash_symm hf)).2
  obtain ⟨σ₂, hσ₂, hσ₂σ⟩ :=
    (ResU.CompS.assoc ρf ρ₂ (ResU.single l (CellU.ownOf v)) σ).mp
      ⟨ρ, ResU.CompS.comm hcρ, hσ⟩
  obtain ⟨hlv, μ₂, hlow₂, hupd, hnone⟩ := lower_compS_own_inv hσ₂σ hμ
  have hdel : BoCa.BoLo.Heap.del μ l = μ₂ := by
    funext k
    by_cases e : k = l
    · subst e; rw [BoCa.BoLo.Heap.del_same, hnone]
    · rw [BoCa.BoLo.Heap.del_other e, hupd, BoCa.BoLo.Heap.upd_other e]
  refine ⟨⟨_, _, Head.free μ l v hlv⟩, fun μ₁ e₁ hh => ?_⟩
  obtain ⟨u, hu, rfl, rfl⟩ := head_free_inv (ℍ := ℍ) hh
  rw [hlv] at hu
  cases hu
  have hT' : TWNC σ₂ ps (rsOf ls) :=
    TWNC.free hT (ResU.CompS.comm hσ₂σ) (hash_valid_comp h₂ hσ₂)
  refine ⟨v, rfl, ρ₂, PMap.empty, σ₂, σ₂, ρ₂, ps, ls,
    ResU.hash_symm h₂, hσ₂,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp h₂ hσ₂)),
    ResU.comp_empty_right σ₂, ?_, ResU.comp_empty_right ρ₂,
    updVN_of_updV Φ _
      (updV_compS_own (ResU.CompS.comm hcρ) (hash_valid h₂).2 (hash_valid hf).2).symm,
    noOwn_empty, hT',
    tagged_of_ag (fun a ha => (own_cell_ag (ResU.CompS.comm hσ₂σ) a).mpr ha) htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, hQ⟩
  rw [hdel]; exact hlow₂

/-- A load's head steps: the location's contents, the memory kept. -/
theorem head_load_inv {μ μ' : Heap} {ℓ : Loc} {a' : Expr}
    (h : Head (ℍ := ℍ) μ (.app (.val (.prim .load)) (.val (Val.loc ℓ))) μ' a') :
    ∃ u, μ ℓ = some u ∧ μ' = μ ∧ a' = .val u := by
  generalize hb : Expr.app (.val (.prim .load)) (.val (Val.loc ℓ)) = b at h
  cases h with
  | load k u hk =>
      simp only [Expr.val, Val.prim, Val.loc, Expr.app.injEq, Expr.loc.injEq, true_and] at hb
      subst hb
      exact ⟨u, hk, rfl, rfl⟩
  | _ => simp_all [hndE, ubindE, ccatchE, cfinE, Expr.val, Val.prim]

/-- **`[TR]` 6.143 (`wp-load`) at the step index** (`wpTS_load`). -/
theorem rwp_load {Φ : LocFam} (ls : List SRec) (l : BoCa.Loc) (v : Val) (Q : PostN) {n : Nat}
    {ρ : WRes} (h : (sep (ptoOwn l v) (wand (ptoOwn l v) (Q (n - 1) ls v))) ρ) :
    rwp (ℍ := ℍ) Φ Q n ls (.app (.val (.prim .load)) (.val (.loc l))) ρ := by
  obtain ⟨ρ₁, ρ₂, hcρ, rfl, hwand⟩ := h
  refine rwp_head1 (Head.load (fun _ => some Val.unit) l Val.unit rfl)
    (fun ρf σ ps μ hf hσ hT htg hμ hfin => ?_)
  have hρ : ρ.get l = some (CellU.ownOf v) := by
    rw [ResU.Comp.get_of_right_none hcρ (ResU.compatS_single_own hcρ.1),
      ResU.single_get_self]
  have hlv : μ l = some v :=
    lower_get_own hμ (by
      rw [ResU.Comp.get_of_left_none hσ (get_eq_none_of_compatS_own
        (ResU.CompatS.symm hf.1) hρ)]
      exact hρ)
  refine ⟨⟨_, _, Head.load μ l v hlv⟩, fun μ₁ e₁ hh => ?_⟩
  obtain ⟨u, hu, rfl, rfl⟩ := head_load_inv hh
  rw [hlv] at hu
  cases hu
  exact ⟨v, rfl, ρ, PMap.empty, σ, σ, ρ, ps, ls,
    ResU.hash_symm hf, hσ,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hf hσ)),
    ResU.comp_empty_right σ, hμ, ResU.comp_empty_right ρ,
    UpdVN.refl Φ _ (hash_valid hf).2, noOwn_empty, hT, htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, hwand _ ρ rfl (ResU.CompS.comm hcρ)⟩

/-- **`[TR]` 6.144 (`wp-load-I`) at the step index** (`wpTS_load_I`). -/
theorem rwp_load_I {Φ : LocFam} (ls : List SRec) (l : BoCa.Loc) (α : Life) (P : Val → WProp)
    (Q : PostN) {n : Nat} {ρ : WRes}
    (h : (sep (ptoImm l α P)
        (all fun v =>
          wand (ptoImm l α (fun v' => sep (pure (v = v')) (P v))) (Q (n - 1) ls v))) ρ) :
    rwp (ℍ := ℍ) Φ Q n ls (.app (.val (.prim .load)) (.val (.loc l))) ρ := by
  obtain ⟨ρ₁, ρR, hcρ, ⟨s, v, σ, hs, rfl, hP, hα⟩, hR⟩ := h
  have hcell : ptoImm l α (fun v' => sep (pure (v = v')) (P v))
      (ResU.single l (CellU.immOf s v σ hs)) :=
    ⟨s, v, σ, hs, rfl, (pure_sep_biEntails rfl (P v)).2 σ hP, hα⟩
  have hQ : Q (n - 1) ls v ρ := hR v _ ρ hcell (ResU.CompS.comm hcρ)
  refine rwp_head1 (Head.load (fun _ => some Val.unit) l Val.unit rfl)
    (fun ρf τ ps μ hf hτ hT htg hμ hfin => ?_)
  obtain ⟨χ, hχ, heχ⟩ := compS_get_erase hcρ (ResU.single_get_self l _)
  obtain ⟨χ', hχ', heχ'⟩ := compS_get_erase (ResU.CompS.comm hτ) hχ
  have hlv : μ l = some v := by
    rw [lower_get hμ hχ', heχ', heχ]
    rfl
  refine ⟨⟨_, _, Head.load μ l v hlv⟩, fun μ₁ e₁ hh => ?_⟩
  obtain ⟨u, hu, rfl, rfl⟩ := head_load_inv hh
  rw [hlv] at hu
  cases hu
  exact ⟨v, rfl, ρ, PMap.empty, τ, τ, ρ, ps, ls,
    ResU.hash_symm hf, hτ,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hf hτ)),
    ResU.comp_empty_right τ, hμ, ResU.comp_empty_right ρ,
    UpdVN.refl Φ _ (hash_valid hf).2, noOwn_empty, hT, htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, hQ⟩

/-- A store's head steps: the location held, overwritten, answering `()`. -/
theorem head_store_inv {μ μ' : Heap} {ℓ : Loc} {v : Val} {a' : Expr}
    (h : Head (ℍ := ℍ) μ (.app (.val (.storeV (.loc ℓ))) (.val v)) μ' a') :
    (∃ w, μ ℓ = some w) ∧ μ' = μ.upd ℓ v ∧ a' = .val .unit := by
  generalize hb : Expr.app (.val (.storeV (.loc ℓ))) (.val v) = b at h
  cases h with
  | store k u w hk =>
      simp only [Expr.val, Val.storeV, Val.prim, Val.loc, Expr.app.injEq, Expr.loc.injEq,
        true_and] at hb
      obtain ⟨rfl, hv⟩ := hb
      obtain rfl : v = u := Subtype.ext hv
      exact ⟨⟨w, hk⟩, rfl, rfl⟩
  | _ => simp_all [hndE, ubindE, ccatchE, cfinE, Expr.val, Val.prim, Val.storeV]

/-- **`[TR]` 6.145 (`wp-store`) at the step index** (`wpTS_store`). -/
theorem rwp_store {Φ : LocFam} (ls : List SRec) (l : BoCa.Loc) (v₁ v₂ : Val) (Q : PostN)
    {n : Nat} {ρ : WRes}
    (h : (sep (ptoOwn l v₁) (wand (ptoOwn l v₂) (Q (n - 1) ls .unit))) ρ) :
    rwp (ℍ := ℍ) Φ Q n ls (.app (.val (.storeV (.loc l))) (.val v₂)) ρ := by
  obtain ⟨ρ₁, ρ₂, hcρ, rfl, hwand⟩ := h
  refine rwp_head1 (Head.store (fun _ => some Val.unit) l v₂ Val.unit rfl)
    (fun ρf σ ps μ hf hσ hT htg hμ hfin => ?_)
  have h₂ : ResU.Hash ρf ρ₂ :=
    ResU.hash_symm (ResU.Hash.split hcρ (ResU.hash_symm hf)).2
  obtain ⟨σ₂, hσ₂, hσ₂σ⟩ :=
    (ResU.CompS.assoc ρf ρ₂ (ResU.single l (CellU.ownOf v₁)) σ).mp
      ⟨ρ, ResU.CompS.comm hcρ, hσ⟩
  obtain ⟨hlv, μ₂, hlow₂, hupd, hnone⟩ := lower_compS_own_inv hσ₂σ hμ
  obtain ⟨x, hx⟩ := (ResU.compS_defined_iff ρ₂ (ResU.single l (CellU.ownOf v₂))).mpr
    (compatS_single_of_get_none (ResU.compatS_single_own hcρ.1))
  obtain ⟨σ', hσ'x, hfx, hlow'⟩ := hash_compS_own hσ₂ hlow₂ hnone hx
  have hstep : BoCa.BoLo.Heap.upd μ l v₂ = BoCa.BoLo.Heap.upd μ₂ l v₂ := by
    funext k
    by_cases e : k = l
    · subst e; rw [BoCa.BoLo.Heap.upd_same, BoCa.BoLo.Heap.upd_same]
    · rw [BoCa.BoLo.Heap.upd_other e, BoCa.BoLo.Heap.upd_other e, hupd,
        BoCa.BoLo.Heap.upd_other e]
  obtain ⟨y, hy, hyσ'⟩ := (ResU.CompS.assoc ρf ρ₂ (ResU.single l (CellU.ownOf v₂)) σ').mp
    ⟨x, hx, hσ'x⟩
  cases ResU.CompS.functional hy hσ₂
  refine ⟨⟨_, _, Head.store μ l v₂ v₁ hlv⟩, fun μ₁ e₁ hh => ?_⟩
  obtain ⟨-, rfl, rfl⟩ := head_store_inv hh
  have hT' : TWNC σ' ps (rsOf ls) :=
    TWNC.store hT (ResU.CompS.comm hσ₂σ) (ResU.CompS.comm hyσ') (hash_valid_comp hfx hσ'x)
  refine ⟨⟨.unit, Val.unit.2⟩, rfl, x, PMap.empty, σ', σ', x, ps, ls,
    ResU.hash_symm hfx, hσ'x,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hfx hσ'x)),
    ResU.comp_empty_right σ', ?_, ResU.comp_empty_right x, ?_,
    noOwn_empty, hT',
    tagged_of_ag (fun a ha => (own_cell_ag (ResU.CompS.comm hσ₂σ) a).mpr
      ((own_cell_ag (ResU.CompS.comm hyσ') a).mp ha)) htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, hwand _ x rfl hx⟩
  · rw [hstep]; exact hlow'
  · exact updVN_of_updV Φ _ (ResU.UpdV.trans
      (updV_compS_own (ResU.CompS.comm hcρ) (hash_valid h₂).2 (hash_valid hf).2).symm
      (updV_compS_own hx (hash_valid h₂).2 (hash_valid hfx).2))

end BoCa.Fig16.LogRel.Core.Chain.SI

end
