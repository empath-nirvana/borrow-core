import TypedCasePort.HandleX

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
