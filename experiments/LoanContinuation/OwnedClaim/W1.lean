import Core.Chain.SI.HandleX

/-! Isolated owned-loan experiment [spec §62].
Adds owned registry fragments, generic frame-preserving loan allocation/closure, and a
branded flat-family continuation protocol over the EXISTING masked erwpX relation. The real
captured continuation is heap-stored across unrelated allocation and an additional park stop.
Preserves existing erwpX unchanged; does not claim Goal791N U/cN or HandlerLawN integration.
Open: arbitrary LocTy/higher-order families, cancellation, general scheduler and adequacy.
-/
noncomputable section
namespace BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open Classical
abbrev Registry := Loc → Option Ret
@[simp] theorem pos_indicator (p : Prop) [Decidable p] :
    0 < (if p then 1 else 0 : Nat) ↔ p := by
  by_cases h : p <;> simp [h]

def reg (m : Registry) : GRes := { (0 : GRes) with auth := fun m' => if m' = m then 1 else 0 }
def claim (γ : Loc) (d : Ret) : GRes :=
  { (0 : GRes) with tokF := fun a r => if a = γ ∧ r = d then 1 else 0 }
def permit (γ : Loc) (d : Ret) : GRes :=
  { (0 : GRes) with wrF := fun a r => if a = γ ∧ r = d then 1 else 0 }
def put (m : Registry) (γ : Loc) (d : Ret) : Registry := fun a => if a = γ then some d else m a

def FP (g h : GRes) : Prop := ∀ f, (f + g).Valid → (f + h).Valid

@[simp] theorem reg_tok (m : Registry) (a : Life) : (reg m).tok a = 0 := rfl
@[simp] theorem claim_tok (γ : Loc) (d : Ret) (a : Life) : (claim γ d).tok a = 0 := rfl
@[simp] theorem permit_tok (γ : Loc) (d : Ret) (a : Life) : (permit γ d).tok a = 0 := rfl

/-- A frame beside the sole authority owns no authoritative component itself. -/
theorem frame_auth_zero {m : Registry} {f : GRes} (hv : (f + reg m).Valid) :
    ∀ m', f.auth m' = 0 := by
  intro m'
  have hz : f.auth m = 0 := by
    have h := hv.auth_le m
    simp [reg] at h
    exact h
  by_contra hn
  have he : m' = m := hv.auth_one m' m (by
    simp only [GRes.auth_add]; exact lt_of_lt_of_le (Nat.pos_of_ne_zero hn) (Nat.le_add_right _ _))
    (by simp [reg])
  exact hn (he ▸ hz)

theorem frame_tok_agree {m : Registry} {f : GRes} (hv : (f + reg m).Valid)
    {a : Loc} {d : Ret} (hp : 0 < f.tokF a d) : m a = some d :=
  hv.tokF_agree m a d (by simp [reg]) (by simpa [reg] using hp)

theorem frame_wr_agree {m : Registry} {f : GRes} (hv : (f + reg m).Valid)
    {a : Loc} {d : Ret} (hp : 0 < f.wrF a d) : m a = some d :=
  hv.wrF_agree m a d (by simp [reg]) (by simpa [reg] using hp)

/-- Fresh allocation creates the lender and borrower halves together. -/
theorem allocate (m : Registry) (γ : Loc) (d : Ret) (hfresh : m γ = none) :
    FP (reg m) (reg (put m γ d) + claim γ d + permit γ d) := by
  intro f hv
  have ha := frame_auth_zero hv
  have hft : ∀ r, f.tokF γ r = 0 := by
    intro r
    by_contra hn
    have hh := frame_tok_agree hv (Nat.pos_of_ne_zero hn)
    rw [hfresh] at hh
    cases hh
  have hfw : ∀ r, f.wrF γ r = 0 := by
    intro r
    by_contra hn
    have hh := frame_wr_agree hv (Nat.pos_of_ne_zero hn)
    rw [hfresh] at hh
    cases hh
  have hvf := GRes.Valid.left hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; simpa [reg, claim, permit] using hvf.tok a
  · intro a; simpa [reg, claim, permit] using hvf.xm a
  · intro m'; simp [reg, claim, permit, ha]; split <;> omega
  · intro m₁ m₂ h₁ h₂
    simp [reg, claim, permit, ha] at h₁ h₂
    exact h₁.trans h₂.symm
  · intro a r
    by_cases he : a = γ
    · subst a; simp [reg, claim, permit, hft]; split <;> omega
    · simpa [reg, claim, permit, he] using hvf.tokF_le a r
  · intro a r r' h₁ h₂
    by_cases he : a = γ
    · subst a
      have h₁' : r = d := by simpa [reg, claim, permit, hft] using h₁
      have h₂' : r' = d := by simpa [reg, claim, permit, hft] using h₂
      exact h₁'.trans h₂'.symm
    · exact hvf.tokF_one a r r' (by simpa [reg, claim, permit, he] using h₁)
        (by simpa [reg, claim, permit, he] using h₂)
  · intro a r
    by_cases he : a = γ
    · subst a; simp [reg, claim, permit, hfw]; split <;> omega
    · simpa [reg, claim, permit, he] using hvf.wrF_le a r
  · intro a r r' h₁ h₂
    by_cases he : a = γ
    · subst a
      have h₁' : r = d := by simpa [reg, claim, permit, hfw] using h₁
      have h₂' : r' = d := by simpa [reg, claim, permit, hfw] using h₂
      exact h₁'.trans h₂'.symm
    · exact hvf.wrF_one a r r' (by simpa [reg, claim, permit, he] using h₁)
        (by simpa [reg, claim, permit, he] using h₂)
  · intro m' a r hm hr
    have hm' : m' = put m γ d := by simpa [reg, claim, permit, ha] using hm
    subst m'
    by_cases he : a = γ
    · subst a
      have hr' : r = d := by simpa [reg, claim, permit, hft] using hr
      subst r; simp [put]
    · have hr' : 0 < f.tokF a r := by simpa [reg, claim, permit, he] using hr
      simpa [put, he] using frame_tok_agree hv hr'
  · intro m' a r hm hr
    have hm' : m' = put m γ d := by simpa [reg, claim, permit, ha] using hm
    subst m'
    by_cases he : a = γ
    · subst a
      have hr' : r = d := by simpa [reg, claim, permit, hfw] using hr
      subst r; simp [put]
    · have hr' : 0 < f.wrF a r := by simpa [reg, claim, permit, he] using hr
      simpa [put, he] using frame_wr_agree hv hr'
  · simpa [reg, claim, permit] using hvf.fin

theorem reg_valid (m : Registry) : (reg m).Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; simp [reg]
  · intro a; simp [reg]
  · intro m'; simp [reg]; split <;> omega
  · intro m₁ m₂ h₁ h₂
    have he₁ : m₁ = m := by simpa [reg] using h₁
    have he₂ : m₂ = m := by simpa [reg] using h₂
    exact he₁.trans he₂.symm
  · intro a r; simp [reg]
  · intro a r r' h; simp [reg] at h
  · intro a r; simp [reg]
  · intro a r r' h; simp [reg] at h
  · intro m' a r _ h; simp [reg] at h
  · intro m' a r _ h; simp [reg] at h
  · simp [reg]

theorem registered_valid (m : Registry) (γ : Loc) (d : Ret) (hm : m γ = some d) :
    (reg m + claim γ d + permit γ d).Valid := by
  let old : Registry := fun a => if a = γ then none else m a
  have he : put old γ d = m := by
    funext a
    by_cases ha : a = γ
    · subst a; simpa [put, old] using hm.symm
    · simp [put, old, ha]
  have hh := allocate old γ d (by simp [old]) 0 (by simpa using reg_valid old)
  simpa [he] using hh

/-- Both halves are necessary to retire an entry while retaining the authority. -/
theorem close (m : Registry) (γ : Loc) (d : Ret) :
    FP (reg m + claim γ d + permit γ d) (reg (put m γ [])) := by
  intro f hv
  have hvR : (f + reg m).Valid := GRes.Valid.left
    (show ((f + reg m) + (claim γ d + permit γ d)).Valid by
      simpa only [GRes.add_assoc] using hv)
  have ha := frame_auth_zero hvR
  have hvf := GRes.Valid.left hv
  have hft : ∀ r, f.tokF γ r = 0 := by
    intro r
    by_cases he : r = d
    · subst r
      have h := hv.tokF_le γ d
      simp [reg, claim, permit] at h
      exact h
    · by_contra hn
      have hh := hv.tokF_one γ r d (by
        simpa [reg, claim, permit, he] using Nat.pos_of_ne_zero hn) (by simp [reg, claim, permit])
      exact he hh
  have hfw : ∀ r, f.wrF γ r = 0 := by
    intro r
    by_cases he : r = d
    · subst r
      have h := hv.wrF_le γ d
      simp [reg, claim, permit] at h
      exact h
    · by_contra hn
      have hh := hv.wrF_one γ r d (by
        simpa [reg, claim, permit, he] using Nat.pos_of_ne_zero hn) (by simp [reg, claim, permit])
      exact he hh
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; simpa [reg] using hvf.tok a
  · intro a; simpa [reg] using hvf.xm a
  · intro m'; simp [reg, ha]; split <;> omega
  · intro m₁ m₂ h₁ h₂
    have he₁ : m₁ = put m γ [] := by simpa [reg, ha] using h₁
    have he₂ : m₂ = put m γ [] := by simpa [reg, ha] using h₂
    exact he₁.trans he₂.symm
  · intro a r; simpa [reg] using hvf.tokF_le a r
  · intro a r r' h₁ h₂
    exact hvf.tokF_one a r r' (by simpa [reg] using h₁) (by simpa [reg] using h₂)
  · intro a r; simpa [reg] using hvf.wrF_le a r
  · intro a r r' h₁ h₂
    exact hvf.wrF_one a r r' (by simpa [reg] using h₁) (by simpa [reg] using h₂)
  · intro m' a r hm hr
    have hm' : m' = put m γ [] := by simpa [reg, ha] using hm
    subst m'
    have hr' : 0 < f.tokF a r := by simpa [reg] using hr
    have hne : a ≠ γ := by intro he; subst a; rw [hft] at hr'; omega
    simpa [put, hne] using frame_tok_agree hvR hr'
  · intro m' a r hm hr
    have hm' : m' = put m γ [] := by simpa [reg, ha] using hm
    subst m'
    have hr' : 0 < f.wrF a r := by simpa [reg] using hr
    have hne : a ≠ γ := by intro he; subst a; rw [hfw] at hr'; omega
    simpa [put, hne] using frame_wr_agree hvR hr'
  · simpa [reg] using hvf.fin

theorem FP.frame {g h : GRes} (hf : FP g h) (b : GRes) : FP (g + b) (h + b) := by
  intro f hv
  have hh := hf (f + b) (by simpa only [GRes.add_assoc, GRes.add_comm, GRes.add_left_comm] using hv)
  simpa only [GRes.add_assoc, GRes.add_comm, GRes.add_left_comm] using hh

/-- Registry agreement couples κ's lender fragment to the returned borrower fragment. -/
theorem match_return {m : Registry} {γ : Loc} {d d' : Ret}
    (hv : (reg m + claim γ d + permit γ d').Valid) : d = d' := by
  have ht := hv.tokF_agree m γ d (by simp [reg, claim, permit]) (by simp [reg, claim, permit])
  have hw := hv.wrF_agree m γ d' (by simp [reg, claim, permit]) (by simp [reg, claim, permit])
  exact Option.some.inj (ht.symm.trans hw)

/-- A pending lender fragment cannot coexist with the authoritative retired entry,
including when the fragment was hidden in garbage. -/
theorem no_pending_after_close (m : Registry) (γ : Loc) (d : Ret) (hd : d ≠ []) :
    ¬ (reg (put m γ []) + claim γ d).Valid := by
  intro hv
  have ht := hv.tokF_agree (put m γ []) γ d
    (by simp [reg, claim]) (by simp [reg, claim])
  have he : ([] : Ret) = d := Option.some.inj (by simpa [put] using ht)
  exact hd he.symm

theorem future_family {m : Registry} {γ : Loc} {d : Ret}
    (hv : (reg m + claim γ d).Valid) : m γ = some d :=
  hv.tokF_agree m γ d (by simp [reg, claim]) (by simp [reg, claim])

/-- Without the borrower permission an adversarial frame prevents authoritative close. -/
theorem close_without_return_impossible (m : Registry) (γ : Loc) (d : Ret)
    (hm : m γ = some d) (hd : d ≠ []) :
    ¬ FP (reg m + claim γ d) (reg (put m γ [])) := by
  intro hf
  have hv := hf (permit γ d) (by
    simpa only [GRes.add_assoc, GRes.add_comm, GRes.add_left_comm] using registered_valid m γ d hm)
  have hw := hv.wrF_agree (put m γ []) γ d
    (by simp [reg, permit]) (by simp [reg, permit])
  have he : ([] : Ret) = d := Option.some.inj (by simpa [put] using hw)
  exact hd he.symm

/-- A fresh registry slot can be added while any existing κ fragments remain in the frame. -/
theorem extend (m : Registry) (γ : Loc) (d : Ret) (hfresh : m γ = none) :
    FP (reg m) (reg (put m γ d)) := by
  intro f hv
  have hh := allocate m γ d hfresh f hv
  exact GRes.Valid.left (show ((f + reg (put m γ d)) + (claim γ d + permit γ d)).Valid by
    simpa only [GRes.add_assoc] using hh)

#print axioms future_family
#print axioms close_without_return_impossible
#print axioms extend
#print axioms allocate
#print axioms close
#print axioms registered_valid
#print axioms match_return
#print axioms no_pending_after_close
end BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan


/-! Generic registry-ghost updates inside the existing masked execution relation.
Updates preserve lifetime counts and mutable masking authorities. No execution rule is assumed.
-/
noncomputable section
namespace BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- Any frame-preserving registry update transports an X run backwards. -/
theorem rwpGX_ghost_update {g h : GRes}
    (hup : ∀ f, (f + g).Valid → (f + h).Valid)
    (htok : g.tok = h.tok) (hxm : g.xm = h.xm)
    {Φ : LocFam} {M : Mask} {Q : PostGX} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes}
    (hrun : rwpGX (ℍ := ℍ) Φ M Q n ls e (ρ, h)) :
    rwpGX (ℍ := ℍ) Φ M Q n ls e (ρ, g) := by
  intro xf fρ ps μ hf hc hv hwf hwx hsh hma hoff htw htag hlow hfd j μ' e' hj hs
  have hC : (xf.2 + h).counted = (xf.2 + g).counted := by
    ext α
    simp only [GRes.counted, Set.mem_ofPred_eq, GRes.tok_add, ← htok]
  have hwf' : WFC (xf.2 + h).counted xf := by rwa [hC]
  have hwx' : WFC (xf.2 + h).counted (ρ, h) := by
    intro α hα hcar
    rw [hC] at hα
    have hh := hwx α hα hcar
    change 0 < h.tok α
    rw [← htok]
    exact hh
  have hma' : MaskAuth M h := by
    intro l a ha
    have hh := hma l a ha
    cases a <;> simpa only [Auth.Held, ← htok, ← hxm] using hh
  have hr := hrun xf fρ ps μ hf hc (hup xf.2 hv) hwf' hwx' hsh hma' hoff
    htw htag hlow hfd j μ' e' hj hs
  refine ⟨hr.1, fun hfin => ?_⟩
  simpa only [EndOKX, Prod.fst, Prod.snd, hC] using hr.2 hfin

/-- The same update at the recursive effectful relation, for arbitrary stop tables and posts. -/
theorem erwpX_ghost_update {g h : GRes}
    (hup : ∀ f, (f + g).Valid → (f + h).Valid)
    (htok : g.tok = h.tok) (hxm : g.xm = h.xm)
    {Φ : LocFam} {M : Mask} {Tb : TableX} {Q : PostX} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes}
    (hrun : erwpX (ℍ := ℍ) Φ M Tb Q n ls e (ρ, h)) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls e (ρ, g) := by
  rw [erwpX_eq] at hrun ⊢
  exact rwpGX_ghost_update hup htok hxm hrun

#print axioms rwpGX_ghost_update
#print axioms erwpX_ghost_update
end BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
end

noncomputable section
namespace BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- The run itself supplies validity of its local ghost resource; clients need not assume it. -/
theorem rwpGX_ghost_valid {Φ : LocFam} {M : Mask} {Q : PostGX}
    {n : Nat} {ls : List SRec} {e : Expr} {x : XRes}
    (h : x.2.Valid → rwpGX (ℍ := ℍ) Φ M Q n ls e x) :
    rwpGX (ℍ := ℍ) Φ M Q n ls e x := by
  intro xf fρ ps μ hf hc hv hwf hwx hsh hma hoff htw htag hlow hfd j μ' e' hj hs
  exact h (GRes.Valid.right hv) xf fρ ps μ hf hc hv hwf hwx hsh hma hoff
    htw htag hlow hfd j μ' e' hj hs

/-- Registry agreement can be derived under the actual erwpX validity guard. -/
theorem erwpX_ghost_valid {Φ : LocFam} {M : Mask} {Tb : TableX} {Q : PostX}
    {n : Nat} {ls : List SRec} {e : Expr} {x : XRes}
    (h : x.2.Valid → erwpX (ℍ := ℍ) Φ M Tb Q n ls e x) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls e x := by
  rw [erwpX_eq]
  apply rwpGX_ghost_valid
  intro hv
  have hh := h hv
  rwa [erwpX_eq] at hh

#print axioms rwpGX_ghost_valid
#print axioms erwpX_ghost_valid
end BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
end

/-! Generic derived rules used by the owned-loan experiment. -/
noncomputable section
namespace BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont Head performE opPayload freeE)
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- An ordinary operation stop at its segment's mask, using its actual table contract. -/
theorem erwpX_perform_same {Φ : LocFam} {M : Mask} {T : OpTabX} {Q : PostX}
    {n : Nat} {ls : List SRec} (K : Kont) {m i : UInt32} {v : Val} {en : OpEntX} {x : XRes}
    (hK : K.HasHnd m = false) (hT : T m i = some en)
    (h : sepX (en.PA n ls v)
      (contShareX en n ls K (erwpXC (ℍ := ℍ) Φ (opTableX T) Q n M)) x) :
    erwpX (ℍ := ℍ) Φ M (opTableX T) Q n ls
      (K.plug (performE (.val (opPayload m i v)))) x := by
  rw [erwpX_eq]
  refine rwpGX_here (final_opPlug (r := false) (payloadName_opPayload m i v) hK) ?_
  intro C
  exact Or.inr ⟨K, m, i, v, en, rfl, hK, hT, Or.inr rfl, h⟩

def park8E : Expr := performE (.val (opPayload 8 0 Val.unit))

/-- Store κ, perform independent allocation, and suspend while κ remains heap-stored. -/
def storeParkBody : Expr :=
  .seq (freeE (.app (.val (.prim .alloc)) (.val Val.unit)))
    (.seq park8E (freeE (.var 0)))

def storePark (e : Expr) : Expr :=
  .app (.val (.lam storeParkBody)) (.app (.val (.prim .alloc)) e)

/-- The storage prefix leaves its owned cell in the actual park continuation.
The supplied park judgment must be established from the chosen table's stop rule. -/
theorem storePark_compat {Φ : LocFam} (hΦ : Φ.Down) {M : Mask} {Tb : TableX}
    (hL : Tb.Local) (hD : Tb.Down) {Q : PostX} (hQ : Q.Down)
    (K : Kont) (v : Val) {n : Nat} {ls : List SRec} {ρ : WRes} {g : GRes}
    (hpark : ∀ a ρa, ResU.CompS (ResU.single a (CellU.ownOf v)) ρ ρa →
      erwpX (ℍ := ℍ) Φ M Tb Q (n - 1 - 1 - 1) ls
        ((K.comp (.seq .hole (freeE (.val (Val.loc a))))).plug park8E) (ρa, g)) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls (K.plug (storePark v.1)) (ρ, g) := by
  change erwpX Φ M Tb Q n ls
    (K.plug ((Kont.appR (.val (.lam storeParkBody)) .hole).plug
      (.app (.val (.prim .alloc)) v.1))) (ρ, g)
  rw [← Kont.plug_comp]
  refine erwpX_alloc hΦ hL _ v (fun a ρa ha => ?_)
  rw [Kont.plug_comp]
  refine erwpX_det hΦ hD hQ (fun μ => step1Only_plug (Head.beta μ storeParkBody (Val.loc a)) rfl K) ?_
  change erwpX Φ M Tb Q (n - 1) ls
    (K.plug ((Kont.seq (.appR (.val (.prim .free)) .hole)
      (.seq park8E (freeE (.val (Val.loc a))))).plug
      (.app (.val (.prim .alloc)) (.val Val.unit)))) (ρa, g)
  rw [← Kont.plug_comp]
  refine erwpX_alloc hΦ hL _ Val.unit (fun b ρb hb => ?_)
  rw [Kont.plug_comp]
  change erwpX Φ M Tb Q (n - 1 - 1) ls
    (K.plug ((Kont.seq .hole (.seq park8E (freeE (.val (Val.loc a))))).plug
      (freeE (.val (Val.loc b))))) (ρb, g)
  rw [← Kont.plug_comp]
  refine erwpX_free hΦ hL _ b Val.unit hb ?_
  rw [Kont.plug_comp]
  refine erwpX_det hΦ hD hQ (fun μ => step1Only_plug (Head.seq μ _) rfl K) ?_
  simpa only [Kont.plug_comp, Kont.plug] using hpark a ρa ha

/-- On a unit answer to park, retrieve κ from storage, at whichever ghost the park returned. -/
theorem storePark_finish {Φ : LocFam} (hΦ : Φ.Down) {M : Mask} {Tb : TableX}
    (hL : Tb.Local) (hD : Tb.Down) {Q : PostX} (hQ : Q.Down)
    (K : Kont) (a : Loc) (v : Val) {n : Nat} {ls : List SRec} {ρ ρa : WRes} {g : GRes}
    (ha : ResU.CompS (ResU.single a (CellU.ownOf v)) ρ ρa)
    (h : erwpX (ℍ := ℍ) Φ M Tb Q (n - 1) ls (K.plug v.1) (ρ, g)) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls
      ((K.comp (.seq .hole (freeE (.val (Val.loc a))))).plug (.val Val.unit)) (ρa, g) := by
  rw [Kont.plug_comp]
  refine erwpX_det hΦ hD hQ (fun μ => step1Only_plug (Head.seq μ _) rfl K) ?_
  exact erwpX_free hΦ hL K a v ha h

#print axioms erwpX_perform_same
#print axioms storePark_compat
#print axioms storePark_finish
end BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
end
namespace BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open Classical
open BoCa.BoLo (Kont Head freeE hndE hndVal performE opPayload)
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

def cellOf : Loan → Val → WRes → Prop
  | .mut l β P, w, ρ => ∃ (u : Val) (h : ResU.InStratum β (PMap.empty : WRes))
      (hu : P u ⟨PMap.empty, h⟩), w = Val.loc l ∧
        ρ = ResU.single l (CellU.mutOf β u PMap.empty h P hu)
  | .imm _ _, _, _ => False

/-- A branded semantic argument: the descriptor and physical loan are coupled to the
borrower fragment. Its identity is subsequently checked against κ's lender fragment. -/
def Returned (γ : Loc) : Nat → List SRec → Val → XProp := fun _ _ w x =>
  ∃ (m : Registry) (d : Loan), cellOf d w x.1 ∧ x.2 = reg m + permit γ [d]

def Outgoing (γ : Loc) : Nat → List SRec → Val → XProp := fun _ _ w x =>
  ∃ (m : Registry) (d : Loan), m γ = some [d] ∧ cellOf d w x.1 ∧ x.2 = reg m + permit γ [d]

def loanEntry (γ : Loc) : OpEntX where
  q := .lin
  remask := false
  PA := Outgoing γ
  PB := Returned γ
  fin := none
  wc := fun ls ls' _ => ls' = ls

/-- The second stop gives the authoritative registry to the resumer; κ's fragments
remain with the parked continuation. The reply may carry an updated registry. -/
def RegistryMsg (γ : Loc) : Nat → List SRec → Val → XProp := fun _ _ w x =>
  w = Val.unit ∧ x.1 = PMap.empty ∧ ∃ m, x.2 = reg m ∧ ∃ d : Loan, m γ = some [d]
def RegistryReply : Nat → List SRec → Val → XProp := fun _ _ w x =>
  w = Val.unit ∧ x.1 = PMap.empty ∧ ∃ m, x.2 = reg m

def parkEntry (γ : Loc) : OpEntX where
  q := .lin
  remask := false
  PA := RegistryMsg γ
  PB := RegistryReply
  fin := none
  wc := fun ls ls' _ => ls' = ls

def parkTab (γ : Loc) : OpTabX := fun m i =>
  if m = 8 ∧ i = 0 then some (parkEntry γ) else none

def loanTab (γ : Loc) : OpTabX := fun m i =>
  if m = 7 ∧ i = 0 then some (loanEntry γ) else parkTab γ m i

def phi : LocFam := fun _ => none
theorem phi_down : phi.Down := fun _ _ _ h => by cases h

def mask (l : Loc) (κ : Life) : Mask := {(l, Auth.mloan κ)}

def finalPost (γ l : Loc) (κ : Life) : PostX := fun _ _ _ w x =>
  w = Val.loc l ∧ ∃ (u : Val) (m : Registry),
    x.1 = ResU.single l (CellU.ownOf u) ∧ x.2 = reg m + GRes.life κ ∧ m γ = some []
theorem finalPost_down (γ l : Loc) (κ : Life) : (finalPost γ l κ).Down := fun _ _ _ _ _ h => h

/-- This is the modeled loan-specific U/arrow protocol. It is an actual recursive
masked execution obligation at every smaller index and every registry supplied by PB.
It is NOT Goal791N's unchanged ordinary U(Mut β A → C). -/
abbrev LoanU (γ : Loc) (M : Mask) (Q : PostX) (k : Nat) (ls : List SRec) (κv : Val) : XProp :=
  KapRelX (ℍ := ℍ) phi M (opTableX (parkTab γ)) Q (loanEntry γ) k ls κv

/-- The family in the authoritative future is derived from the owned claim. -/
theorem returned_match {γ : Loc} {d : Loan} {g : GRes} {k : Nat} {ls : List SRec}
    {w : Val} {x z : XRes} (hR : Returned γ k ls w x)
    (hc : CompX (PMap.empty, claim γ [d] + g) x z) (hv : z.2.Valid) :
    ∃ (m : Registry), m γ = some [d] ∧ cellOf d w x.1 := by
  obtain ⟨m, d', hcell, hg⟩ := hR
  have hv' : (reg m + claim γ [d] + permit γ [d'] + g).Valid := by
    rw [hc.2, hg] at hv
    simpa only [GRes.add_assoc, GRes.add_comm, GRes.add_left_comm] using hv
  have he : d = d' := (List.cons.inj (match_return (GRes.Valid.left hv'))).1
  subst d'
  have hfamily := (GRes.Valid.left (show ((reg m + claim γ [d]) + (permit γ [d] + g)).Valid by
    simpa only [GRes.add_assoc] using hv')).tokF_agree m γ [d]
      (by simp [reg, claim]) (by simp [reg, claim])
  exact ⟨m, hfamily, hcell⟩

/-- Opening now creates an owned registry obligation together with the physical loan. -/
theorem open_owned {m : Registry} {γ l : Loc} {κ β : Life}
    (hfresh : m γ = none) (P : Val → SPropS Loc Val β)
    (hw : P Val.unit ⟨PMap.empty, ResU.inStratum_empty β⟩)
    {Tb : TableX} {Q : PostX} {n : Nat} {ls : List SRec} {e : Expr}
    (h : erwpX (ℍ := ℍ) phi (mask l κ) Tb Q n ls e
      (ResU.single l (CellU.mutOf β Val.unit PMap.empty (ResU.inStratum_empty β) P hw),
        (reg (put m γ [.mut l β P]) + claim γ [.mut l β P] + permit γ [.mut l β P]) + GRes.life κ)) :
    erwpX (ℍ := ℍ) phi (mask l κ) Tb Q n ls e
      (ResU.single l (CellU.ownOf Val.unit), reg m + GRes.life κ) := by
  apply erwpX_ghost_update ((allocate m γ [.mut l β P] hfresh).frame (GRes.life κ))
    (by funext a; simp [reg, claim, permit]) (by funext a; simp [reg, claim, permit])
  refine erwpX_mutLoanOpen (l := l) (κ := κ) (β := β) (P := P)
    (hstr := ResU.inStratum_empty β) (hw := hw) (by simp [mask]) _ ls (ResU.comp_empty_right _) ?_
  intro ρ hρ
  have he := eq_of_compS_empty_left (ResU.CompS.comm hρ)
  simpa only [he] using h

/-- Matched closure consumes both fragments and changes the authoritative entry to retired. -/
theorem close_owned {m : Registry} {γ l : Loc} {κ β : Life}
    (P : Val → SPropS Loc Val β) (u : Val) {h : ResU.InStratum β (PMap.empty : WRes)}
    (hu : P u ⟨PMap.empty, h⟩) {Tb : TableX} {Q : PostX} {n : Nat} {ls : List SRec} {e : Expr}
    (hbody : erwpX (ℍ := ℍ) phi (mask l κ) Tb Q n ls e
      (ResU.single l (CellU.ownOf u), reg (put m γ []) + GRes.life κ)) :
    erwpX (ℍ := ℍ) phi (mask l κ) Tb Q n ls e
      (ResU.single l (CellU.mutOf β u PMap.empty h P hu),
        (reg m + claim γ [.mut l β P] + permit γ [.mut l β P]) + GRes.life κ) := by
  apply erwpX_ghost_update ((close m γ [.mut l β P]).frame (GRes.life κ))
    (by funext a; simp [reg, claim, permit]) (by funext a; simp [reg, claim, permit])
  refine erwpX_mutLoanEnd (l := l) (κ := κ) (β := β) (P := P)
    (hstr := h) (hw := hu) (by simp [mask]) _ ls (ResU.comp_empty_right _) ?_
  intro ρ hρ
  have he := eq_of_compS_empty_left (ResU.CompS.comm hρ)
  simpa only [he] using hbody

#print axioms returned_match
#print axioms open_owned
#print axioms close_owned
end BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan

namespace BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open Classical
open BoCa.BoLo (Kont Head performE opPayload freeE hndE hndVal)
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

def borrowOut (l : Loc) : Expr := performE (.val (opPayload 7 0 (Val.loc l)))

theorem out_opened (m : Registry) (γ l : Loc) (κ β : Life)
    (P : Val → SPropS Loc Val β) (hw : P Val.unit ⟨PMap.empty, ResU.inStratum_empty β⟩)
    (hm : m γ = some [.mut l β P]) (n : Nat) (ls : List SRec) :
    erwpX (ℍ := ℍ) phi (mask l κ) (opTableX (loanTab γ)) (finalPost γ l κ) n ls
      (borrowOut l)
      (ResU.single l (CellU.mutOf β Val.unit PMap.empty (ResU.inStratum_empty β) P hw),
        (reg m + claim γ [.mut l β P] + permit γ [.mut l β P]) + GRes.life κ) := by
  refine erwpX_perform_same (en := loanEntry γ) Kont.hole rfl (by simp [loanTab]) ?_
  refine ⟨_, PMap.empty, reg m + permit γ [.mut l β P],
    claim γ [.mut l β P] + GRes.life κ, ResU.comp_empty_right _, ?_, ?_, ?_⟩
  · simp only [GRes.add_assoc, GRes.add_comm, GRes.add_left_comm]
  · exact ⟨m, .mut l β P, hm, ⟨Val.unit, ResU.inStratum_empty β, hw, rfl, rfl⟩, rfl⟩
  · constructor
    · intro he; cases he
    · intro ls' hls
      have he : ls' = ls := hls
      subst ls'
      constructor
      · intro k hk w y z hB hc
        simp only [erwpXC, hk, if_true]
        apply erwpX_ghost_valid
        intro hv
        obtain ⟨m', d', hcell, hg⟩ := hB
        have hv' : (reg m' + claim γ [.mut l β P] + permit γ [d'] + GRes.life κ).Valid := by
          rw [hc.2, hg] at hv
          simpa only [GRes.add_assoc, GRes.add_comm, GRes.add_left_comm] using hv
        have hd : Loan.mut l β P = d' := (List.cons.inj (match_return (GRes.Valid.left hv'))).1
        subst d'
        obtain ⟨u, h, hu, rfl, hy⟩ := hcell
        have hzρ : z.1 = ResU.single l (CellU.mutOf β u PMap.empty h P hu) :=
          (eq_of_compS_empty_left hc.1).trans hy
        have hzg : z.2 = (reg m' + claim γ [.mut l β P] + permit γ [.mut l β P]) + GRes.life κ := by
          rw [hc.2, hg]
          simp only [GRes.add_assoc, GRes.add_comm, GRes.add_left_comm]
        have hez : z = (ResU.single l (CellU.mutOf β u PMap.empty h P hu),
            (reg m' + claim γ [.mut l β P] + permit γ [.mut l β P]) + GRes.life κ) := Prod.ext hzρ hzg
        rw [hez]
        exact close_owned P u hu (erwpX_val (fun _ => ⟨rfl, u, put m' γ [], rfl, rfl, by simp [put]⟩))
      · intro he; exact (he rfl).elim

/-- Owned claim and return permission are minted by the same rule that opens the loan. -/
theorem borrowOut_owned (m : Registry) (γ l : Loc) (κ β : Life)
    (P : Val → SPropS Loc Val β) (hw : P Val.unit ⟨PMap.empty, ResU.inStratum_empty β⟩)
    (hfresh : m γ = none) (n : Nat) :
    erwpX (ℍ := ℍ) phi (mask l κ) (opTableX (loanTab γ)) (finalPost γ l κ) n []
      (borrowOut l) (ResU.single l (CellU.ownOf Val.unit), reg m + GRes.life κ) := by
  apply open_owned hfresh P hw
  exact out_opened (put m γ [.mut l β P]) γ l κ β P hw (by simp [put]) n []

#print axioms out_opened
#print axioms borrowOut_owned
end BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan

namespace BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open Classical
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

def emptyRegistry : Registry := fun _ => none
def unitPred (β : Life) : Val → SPropS Loc Val β := fun u r => u = Val.unit ∧ r.1 = PMap.empty
def unitLoan (l : Loc) (β : Life) : Loan := .mut l β (unitPred β)
def unitCell (l : Loc) (β : Life) : WRes :=
  ResU.single l (CellU.mutOf β Val.unit PMap.empty (ResU.inStratum_empty β) (unitPred β) ⟨rfl,rfl⟩)
def W0 : Registry := put emptyRegistry 0 [unitLoan 0 1]
/-- A separately opened unrelated loan changes the registry while the first stays live. -/
def W1 : Registry := put W0 1 [unitLoan 1 2]

theorem W1_changed : W1 ≠ W0 := by
  intro he
  have hh := congrArg (fun m : Registry => m 1) he
  simp [W1,W0,put,emptyRegistry] at hh

theorem W1_allowed : FP (reg W0) (reg W1) := extend W0 1 [unitLoan 1 2] (by simp [W0,put,emptyRegistry])

theorem W1_opens_unrelated : FP (reg W0)
    (reg W1 + claim 1 [unitLoan 1 2] + permit 1 [unitLoan 1 2]) :=
  allocate W0 1 [unitLoan 1 2] (by simp [W0,put,emptyRegistry])

theorem W1_all_permissions_valid :
    (reg W1 + claim 0 [unitLoan 0 1] + permit 0 [unitLoan 0 1] +
      claim 1 [unitLoan 1 2] + permit 1 [unitLoan 1 2]).Valid := by
  have hh := W1_opens_unrelated (claim 0 [unitLoan 0 1] + permit 0 [unitLoan 0 1])
    (by simpa only [GRes.add_assoc,GRes.add_comm,GRes.add_left_comm] using
      registered_valid W0 0 [unitLoan 0 1] (by simp [W0,put]))
  simpa only [GRes.add_assoc,GRes.add_comm,GRes.add_left_comm] using hh

theorem W1_preserves_claim : (reg W1 + claim 0 [unitLoan 0 1] + permit 0 [unitLoan 0 1]).Valid :=
  registered_valid W1 0 _ (by simp [W1,W0,put])

theorem W1_park_reply (k : Nat) (ls : List SRec) :
    RegistryReply k ls Val.unit (PMap.empty, reg W1) := ⟨rfl,rfl,W1,rfl⟩

theorem W0_park_payload (k : Nat) (ls : List SRec) :
    RegistryMsg 0 k ls Val.unit (PMap.empty, reg W0) :=
  ⟨rfl,rfl,W0,rfl,unitLoan 0 1,by simp [W0,put]⟩

theorem W1_returned (k : Nat) (ls : List SRec) :
    Returned 0 k ls (Val.loc 0) (unitCell 0 1, reg W1 + permit 0 [unitLoan 0 1]) :=
  ⟨W1,unitLoan 0 1,⟨Val.unit,ResU.inStratum_empty 1,⟨rfl,rfl⟩,rfl,rfl⟩,rfl⟩

theorem positive_initial_ghost (κ : Life) : (reg emptyRegistry + GRes.life κ).Valid := by
  apply GRes.valid_add_life (reg_valid emptyRegistry)
  simp [reg]

theorem positive_W1_ghost (κ : Life) :
    ((reg W1 + claim 0 [unitLoan 0 1] + permit 0 [unitLoan 0 1]) + GRes.life κ).Valid := by
  apply GRes.valid_add_life W1_preserves_claim
  simp [reg,claim,permit]

/-- A different legitimate loan permission is not a γ-branded returned argument. -/
theorem wrong_slot_rejected (γ δ : Loc) (hne : γ ≠ δ) (m : Registry) (d : Loan)
    (w : Val) (ρ : WRes) (k : Nat) (ls : List SRec) :
    ¬ Returned γ k ls w (ρ, reg m + permit δ [d]) := by
  rintro ⟨m',d',_,hg⟩
  have he := congrArg (fun g : GRes => g.wrF γ [d']) hg
  simp [reg,permit,hne] at he

/-- EndOKX cannot certify reclaimed ownership and a retired authority while the
borrower permission remains outside, even though arbitrary garbage ghosts are allowed. -/
theorem terminal_requires_return {M : Mask} {γ l : Loc} {κ : Life} {d : Ret}
    (hd : d ≠ []) {k : Nat} {ls : List SRec} {x : XRes} {ps : List FrameRec}
    {μ : BoLo.Heap} {t : Expr} :
    ¬ EndOKX phi M (valPostX M (finalPost γ l κ)) k ls x
      (PMap.empty, permit γ d) ps μ t := by
  rintro ⟨M',ρ',ρp,fρ',fρ'p,π,g',gp,ps',ls',h1,h2,h3,h4,h5,h6,hU,hNo,
    hTW,hTag,hRec,hList,hV,hNew,hW1,hW2,hSh1,hSh2,hAuth,hOff,hSx,hFx,hQ⟩
  obtain ⟨_,v,_,_,u,m,_,hg,hm⟩ := hQ
  change g' = reg m + GRes.life κ at hg
  subst g'
  have ha : 0 < (permit γ d + ((reg m + GRes.life κ) + gp)).auth m := by
    simp [reg,permit]
  have hw : 0 < (permit γ d + ((reg m + GRes.life κ) + gp)).wrF γ d := by
    simp [reg,permit]
  have hh := hV.wrF_agree m γ d ha hw
  rw [hm] at hh
  exact hd (Option.some.inj hh).symm

#print axioms W1_opens_unrelated
#print axioms W1_all_permissions_valid
#print axioms W1_allowed
#print axioms W1_preserves_claim
#print axioms W1_park_reply
#print axioms W1_returned
#print axioms positive_initial_ghost
#print axioms positive_W1_ghost
#print axioms wrong_slot_rejected
#print axioms terminal_requires_return
end BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan

namespace BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open Classical
open BoCa.BoLo (Kont Head performE opPayload freeE hndE hndVal)
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

theorem parkTab_entry {γ : Loc} {m i : UInt32} {en : OpEntX}
    (h : parkTab γ m i = some en) : m = 8 ∧ i = 0 ∧ en = parkEntry γ := by
  unfold parkTab at h
  split at h
  · rename_i hm
    exact ⟨hm.1, hm.2, (Option.some.inj h).symm⟩
  · cases h

theorem parkTab_down (γ : Loc) : (parkTab γ).Down where
  pa := by
    intro m i en ht k ls v x h
    obtain ⟨_, _, rfl⟩ := parkTab_entry ht
    exact h
  fin := by
    intro m i en P ht hP
    obtain ⟨_, _, rfl⟩ := parkTab_entry ht
    cases hP
  wcl := by
    intro m i en ht ls ls' x₁ x₂ x hc h
    obtain ⟨_, _, rfl⟩ := parkTab_entry ht
    exact h

def storedClause : Val := .lam (.letpair (.var 0)
  (.app (.app (storePark (.var 0)) (.val (Val.inj₁ .unit))) (.var 1)))

/-- A genuine captured continuation is stored while a second operation hands the
registry authority to its resumer. The resumed registry need not equal the old one.
The original loan and return permission remain with the suspended computation. -/
theorem storedClause_compat (γ : Loc) (M : Mask) (Q : PostX) (hQ : Q.Down)
    (k : Nat) (ls : List SRec) (v kv : Val) (x : XRes)
    (hx : sepX ((loanEntry γ).PA k ls v) (LoanU (ℍ := ℍ) γ M Q k ls kv) x) :
    erwpX (ℍ := ℍ) phi M (opTableX (parkTab γ)) Q k ls
      (.app storedClause.1 (.pair v.1 kv.1)) x := by
  cases k with
  | zero => exact erwpX_zero
  | succ k =>
    obtain ⟨ρ, g⟩ := x
    obtain ⟨ρa, ρk, ga, gk, hc, hg, hA, hK⟩ := hx
    obtain ⟨m, d, hmd, hcell, hga⟩ := hA
    change ga = reg m + permit γ [d] at hga
    refine erwpX_det phi_down (opTableX_down (parkTab_down γ)) hQ
      (fun μ => step1Only_plug (Head.beta μ _ (Val.pair v kv)) rfl .hole) ?_
    refine erwpX_det phi_down (opTableX_down (parkTab_down γ)) hQ
      (fun μ => step1Only_plug (Head.letpair μ v kv _) rfl .hole) ?_
    have hh := storePark_compat (ℍ := ℍ) phi_down (M := M)
      (opTableX_local (parkTab γ)) (opTableX_down (parkTab_down γ)) hQ
      (.appL (.appL .hole (Val.inj₁ .unit)) v) kv
      (n := k + 1) (ls := ls) (ρ := ρ) (g := g) (fun a ρheap ha => by
        refine erwpX_perform_same (en := parkEntry γ)
          ((Kont.appL (.appL .hole (Val.inj₁ .unit)) v).comp
            (.seq .hole (freeE (.val (Val.loc a))))) rfl (by simp [parkTab]) ?_
        refine ⟨PMap.empty, ρheap, reg m, permit γ [d] + gk,
          ResU.comp_empty_left _, ?_, ?_, ?_⟩
        · rw [hg, hga]
          exact GRes.add_assoc _ _ _
        · exact ⟨rfl, rfl, m, rfl, d, hmd⟩
        · constructor
          · intro he; cases he
          · intro ls' hls
            have he : ls' = ls := hls
            subst ls'
            constructor
            · intro j hj w y z hB hcz
              simp only [erwpXC, hj, if_true]
              obtain ⟨hw, hyρ, m', hyg⟩ := hB
              subst w
              have hzρ : z.1 = ρheap := by
                have he := hcz.1
                rw [hyρ] at he
                exact eq_of_compS_empty_left (ResU.CompS.comm he)
              have hzg : z.2 = gk + (reg m' + permit γ [d]) := by
                rw [hcz.2, hyg]
                simp only [GRes.add_assoc, GRes.add_comm]
              have hz : z = (ρheap, gk + (reg m' + permit γ [d])) := Prod.ext hzρ hzg
              rw [hz]
              apply storePark_finish phi_down (opTableX_local (parkTab γ))
                (opTableX_down (parkTab_down γ)) hQ
                (.appL (.appL .hole (Val.inj₁ .unit)) v) a kv ha
              exact hK ls rfl (j - 1) (by omega) v
                (ρa, reg m' + permit γ [d]) (ρ, gk + (reg m' + permit γ [d]))
                ⟨m', d, hcell, rfl⟩ ⟨ResU.CompS.comm hc, rfl⟩
            · intro he; exact (he rfl).elim)
    simpa [storedClause, storePark, storeParkBody, park8E, Expr.subst, Expr.shift,
      Expr.val, Val.lam, Val.pair, Val.shift, Val.inj₁, Val.unit, Val.i32, freeE, performE, opPayload,
      Kont.plug, CancelIntercept.subst_shift_one] using hh

#print axioms parkTab_down
#print axioms storedClause_compat
end BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan

namespace BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open Classical
open BoCa.BoLo (Kont Head performE opPayload freeE hndE hndVal)
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

theorem loanTab_caught {γ : Loc} {i : UInt32} {en : OpEntX}
    (h : loanTab γ 7 i = some en) : i = 0 ∧ en = loanEntry γ := by
  by_cases hi : i = 0
  · subst i
    have he : loanEntry γ = en := Option.some.inj (by simpa [loanTab] using h)
    exact ⟨rfl,he.symm⟩
  · simp [loanTab,parkTab,hi] at h

theorem loanTab_down (γ : Loc) : (loanTab γ).Down where
  pa := by
    intro m i en ht k ls v x h
    unfold loanTab at ht
    split at ht
    · cases Option.some.inj ht; exact h
    · exact (parkTab_down γ).pa m i en ht k ls v x h
  fin := by
    intro m i en P ht hp
    unfold loanTab at ht
    split at ht
    · cases Option.some.inj ht; cases hp
    · exact (parkTab_down γ).fin m i en P ht hp
  wcl := by
    intro m i en ht ls ls' x₁ x₂ x hc h
    unfold loanTab at ht
    split at ht
    · cases Option.some.inj ht; exact h
    · exact (parkTab_down γ).wcl m i en ht ls ls' x₁ x₂ x hc h

def handler : Val := hndVal 7 (qualsVal [.lin]) (.lam (.var 0)) (.pair storedClause .unit)
def storedProgram (l : Loc) : Expr := hndE handler (borrowOut l)

/-- Combined masked execution/owned-claim/branded-continuation theorem.
The real captured κ is heap-stored across unrelated allocation AND a second park8 stop.
Park returns an arbitrary authoritative registry compatible with the retained fragments.
The matching loan return retires the registry entry and restores original ownership. -/
theorem storedProgram_owned (m : Registry) (γ l : Loc) (κ β : Life)
    (P : Val → SPropS Loc Val β) (hw : P Val.unit ⟨PMap.empty, ResU.inStratum_empty β⟩)
    (hfresh : m γ = none) (n : Nat) :
    erwpX (ℍ := ℍ) phi (mask l κ) (opTableX (parkTab γ)) (finalPost γ l κ) n []
      (storedProgram l) (ResU.single l (CellU.ownOf Val.unit), reg m + GRes.life κ) := by
  refine erwpX_handle phi_down (loanTab γ) (parkTab γ) (loanTab_down γ) (parkTab_down γ) 7
    (fun m i hm => ?_) (qualsVal [.lin]) (.lam (.var 0)) (.pair storedClause .unit)
    (finalPost γ l κ) (finalPost γ l κ) (finalPost_down γ l κ)
    (fun i en ht => ?_) (fun i en ht => ?_) (fun M C k ls v x h => ?_)
    (fun i en ht => ?_) n (mask l κ) [] (borrowOut l)
    (ResU.single l (CellU.ownOf Val.unit), reg m + GRes.life κ)
    (borrowOut_owned m γ l κ β P hw hfresh n)
  · simp [loanTab,hm]
  · obtain ⟨_,rfl⟩ := loanTab_caught ht
    exact ⟨Or.inl rfl,rfl⟩
  · obtain ⟨rfl,rfl⟩ := loanTab_caught ht
    rfl
  · refine erwpX_det phi_down (opTableX_down (parkTab_down γ)) (finalPost_down γ l κ)
      (fun μ => step1Only_plug (Head.beta μ (.var 0) v) rfl .hole) ?_
    exact erwpX_val (fun _ => h)
  · obtain ⟨rfl,rfl⟩ := loanTab_caught ht
    refine ⟨storedClause, ?_, fun M k ls v kv x hx =>
      storedClause_compat γ M (finalPost γ l κ) (finalPost_down γ l κ) k ls v kv x hx⟩
    simp [BoLo.clauseAt,Val.pair,storedClause,Val.lam,Expr.val,IsVal.lam]

/-- Concrete W1 protocol instance. Its second-stop reply RegistryReply is inhabited by
reg W1, and W1_allowed/W1_preserves_claim certify the resource-derived world change. -/
theorem W1_program (n : Nat) :
    erwpX (ℍ := ℍ) phi (mask 0 0) (opTableX (parkTab 0)) (finalPost 0 0 0) n []
      (storedProgram 0) (ResU.single 0 (CellU.ownOf Val.unit), reg emptyRegistry + GRes.life 0) :=
  storedProgram_owned emptyRegistry 0 0 0 1 (unitPred 1) ⟨rfl,rfl⟩ rfl n

#print axioms loanTab_down
#print axioms storedProgram_owned
#print axioms W1_program
end BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan

namespace BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open Classical
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- Distinct loan identities at the same lifetime can coexist; no global lifetime freeze. -/
theorem two_loans_coexist :
    (reg (put W0 1 [unitLoan 1 1]) + claim 0 [unitLoan 0 1] + permit 0 [unitLoan 0 1] +
      claim 1 [unitLoan 1 1] + permit 1 [unitLoan 1 1]).Valid := by
  have h0 := registered_valid W0 0 [unitLoan 0 1] (by simp [W0,put])
  have hh := allocate W0 1 [unitLoan 1 1] (by simp [W0,put,emptyRegistry])
    (claim 0 [unitLoan 0 1] + permit 0 [unitLoan 0 1])
    (by simpa only [GRes.add_assoc,GRes.add_comm,GRes.add_left_comm] using h0)
  simpa only [GRes.add_assoc,GRes.add_comm,GRes.add_left_comm] using hh

/-- The old same-lifetime/different-location answer is rejected by the branded protocol,
although both legitimate loans may coexist. -/
theorem same_lifetime_wrong_return_rejected (k : Nat) (ls : List SRec) :
    ¬ Returned 0 k ls (Val.loc 1)
      (unitCell 1 1, reg (put W0 1 [unitLoan 1 1]) + permit 1 [unitLoan 1 1]) :=
  wrong_slot_rejected 0 1 (by decide) _ _ _ _ k ls

/-- Relabeling that wrong cell with the expected slot also fails registry agreement. -/
theorem forged_same_slot_rejected :
    ¬ (reg W0 + claim 0 [unitLoan 0 1] + permit 0 [unitLoan 1 1]).Valid := by
  intro hv
  have hh := match_return hv
  have he := (List.cons.inj hh).1
  have hl := congrArg (fun d : Loan => match d with | .mut l _ _ => l | .imm _ _ => 0) he
  simp [unitLoan] at hl

/-- Every accepted extra park exposes an authoritative pending debt. It cannot certify
an erased registry, regardless of what the continuation/garbage predicates happen to be. -/
theorem park_debt_visible {γ : Loc} {M M' : Mask} {C : Set Life} {k : Nat}
    {ls : List SRec} {t : Expr} {Ψ : ContX} {x : XRes}
    (hp : opTableX (parkTab γ) M M' C k ls t Ψ x) :
    ∃ (m : Registry) (d : Loan), 0 < x.2.auth m ∧ m γ = some [d] := by
  obtain ⟨K,n,i,v,en,_,_,ht,_,ρa,ρk,ga,gk,hc,hg,hA,_⟩ := hp
  obtain ⟨_,_,rfl⟩ := parkTab_entry ht
  obtain ⟨_,_,m,hga,d,hm⟩ := hA
  refine ⟨m,d,?_,hm⟩
  change ga = reg m at hga
  rw [hg,hga]
  simp [reg]

#print axioms two_loans_coexist
#print axioms same_lifetime_wrong_return_rejected
#print axioms forged_same_slot_rejected
#print axioms park_debt_visible
end BoCa.Fig16.LogRel.Core.Chain.SI.OwnedLoan

