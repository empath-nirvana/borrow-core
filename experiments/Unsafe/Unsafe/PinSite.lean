import Core.PinLaw

/-!
# Unsafe — R1 at one site  (`docs/unsafe.md` §4, option Q1-D)

`PinStop` quantifies over every body with a `CDerivesP` derivation. `PinSite` is R1's claim at
one lend the checker emitted: the relation at that site's term, with its body `M` and finaliser
`d` fixed. It has no quantifier over code and no premise in `CDerivesP`, so a rule added to
`CDerives` or `CDerivesP` does not change it. `pinSite_of_pinStop`: `PinStop` implies every site
it licenses, so `PinLaw` stays the schema the sites instantiate, and a proof of it discharges
them all.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Unsafe.Pin
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **R1 at one site**: the lend of `r : Ref T` to the body `M`, with the owner's finaliser `d`,
at the row `S`, is in the relation at `F_S (Ref T ⊗ B)`. -/
def PinSite (Δ : LifeCtx) (T B : VTy) (d M : Expr) (S : Row) : Prop :=
  SemC (ℍ := ℍ) Δ [⟨.ref T, true⟩]
    (.app (.app (.val (withborUV d)) (.var 0)) (.val (lendCb M)))
    (CTy.effOf S (.tensor (.ref T) B))

/-- `PinStop` implies the claim at each site whose premises the checker established. -/
theorem pinSite_of_pinStop (h : PinStop (ℍ := ℍ)) {Δ : LifeCtx} {x : LifeVar}
    {b : Lifetime.Life} {T B : VTy} {d M : Expr} {S : Row}
    (h1 : Δ.Defines b) (h2 : Δ.find? x = none) (h3 : b.mentions x = false)
    (h4 : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (h5 : ¬ VFree x T) (h6 : ¬ VFree x B) (h7 : NoThunkT B)
    (h8 : ∃ b', Δ.Defines b' ∧ VOutlivesLe Δ b' T) (h9 : Row.ResumeO S x)
    (h10 : closedAt 1 M = true) (h11 : closedAt 0 (lendCb M).1 = true)
    (h12 : closedAt 0 d = true) (h13 : SemV (ℍ := ℍ) Δ [] d (.lolli (.ref T) .unit))
    (hM : CDerivesP (Δ.extend x b) [⟨.mut (.var x) T, true⟩] M
      (.comp (CTy.effOf S (.box (.var x) B)))) :
    PinSite (ℍ := ℍ) Δ T B d M S :=
  h Δ x b T B d M S h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hM

/-- `PinLaw` implies every site. -/
theorem pinSite_of_pinLaw (h : PinLaw (ℍ := ℍ)) {Δ : LifeCtx} {x : LifeVar}
    {b : Lifetime.Life} {T B : VTy} {d M : Expr} {S : Row}
    (h1 : Δ.Defines b) (h2 : Δ.find? x = none) (h3 : b.mentions x = false)
    (h4 : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (h5 : ¬ VFree x T) (h6 : ¬ VFree x B) (h7 : NoThunkT B)
    (h8 : ∃ b', Δ.Defines b' ∧ VOutlivesLe Δ b' T) (h9 : Row.ResumeO S x)
    (h10 : closedAt 1 M = true) (h11 : closedAt 0 (lendCb M).1 = true)
    (h12 : closedAt 0 d = true) (h13 : SemV (ℍ := ℍ) Δ [] d (.lolli (.ref T) .unit))
    (hM : CDerivesP (Δ.extend x b) [⟨.mut (.var x) T, true⟩] M
      (.comp (CTy.effOf S (.box (.var x) B)))) :
    PinSite (ℍ := ℍ) Δ T B d M S :=
  pinSite_of_pinStop h.stop h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hM

end Unsafe.Pin

end
