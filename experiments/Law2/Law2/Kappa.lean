import Law2.Hereditary

/-!
# Law2 — the suspended continuation re-lends, frame by frame

At a stop the lender ends its lend; at resume it makes the lend afresh at a lifetime beneath the
resumer's list. The suspended continuation `κ = K` must then be related at the moved reading, at
the re-made share. A borrow constant's own callback has this for free at its start: its type
`∀'x ⊏ b. Mut 'x T ⊸ …` is related at every instance. A continuation captured at a stop has no
such clause: `contShare` relates `K` at the reading the run was at.

**The property a resume needs** (`KappaRelends`): at every re-making `θ` of the region (every lend
the stop ended, nested to any depth, moved by one order embedding), the share has a re-make at
which `K`, plugged with any answer related at the moved reading, is related at the moved reading.
It replaces, for a continuation, the `∀'x` a borrow constant reads its callback at.

**Typed continuations re-lend** (`kappa_relend`, `kappaRelends_of_typed`). When `K` is a typed
segment — `K[w] = E[w/z, γ]` for a term `E` Core's typing derives with the hole a variable `z` —
over a hereditarily typed context (`HTG`), `K` re-lends at every re-making: the context re-lends
(`htg_relend`, hereditarily through closures) and the fundamental property relates `E` at the moved
reading, which `⟦Δ⟧` admits. This is `relend_derivable` extended from closed terms to plugged
contexts and from first-order contexts to closures, frame by frame.

What is not derived here is that a continuation captured by a run of a typed program is such a
segment with the share split as its context: the run's relation (`contShare`) states the
continuation's share as one wand, not split by frame. `KappaRelends` is not what D16.1's piece
(`OpenS`) reads either: the piece keeps the frozen share as it is and hands the views afresh at
every re-lend, and on `Life = ℕᵒᵈ` some of those re-lends are not the image of any `Restrat.Emb`
(`relend_not_emb`). (S1) is stated at the piece (`Law2/Target.lean`) and proved at the fragment by
the re-lendable reading `RSlot` (`Law2/Piece.lean`, `Law2/Fragment.lean`), which reads re-lends
directly.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Law2
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Head)
open BoCa.Lifetime (LifeVar LifeCtx LSub)

/-- **A typed segment**: `K` plugged with any value `w` is `E` closed by `w :: γ`, for a term `E`
that Core's typing derives at `C` with the hole a live variable of type `B` in front of `Γ`. -/
def TypedSeg (K : Kont) (Δ : LifeCtx) (Γ : Ctx VTy) (B : VTy) (C : CTy) (γ : List Val) :
    Prop :=
  ∃ E : Expr, CDerives Δ (⟨B, true⟩ :: Γ) E (.comp C) ∧
    ∀ w : Val, K.plug (.val w) = substAll (w :: γ) E

/-- **The property a resume needs**, at one re-making `θ`: the share `ρ` of the continuation `K`,
suspended at the reading `δ`, has a re-make at which `K`, plugged with any answer related at the
moved reading, is related at the moved reading, at every record list. -/
def RelendsAt {c : Life} (θ : Restrat.Emb c) (K : Kont) (B : VTy) (C : CTy) (δ : LSub)
    (ρ : WRes) : Prop :=
  ∃ ρ', RemakeR θ ρ ρ' ∧ ∀ (ls : List SRec) (w : Val) (ρw ρt : WRes),
    vCE (ℍ := ℍ) none true B ls (mv θ δ) w ρw → ResU.CompS ρw ρ' ρt →
      cC (ℍ := ℍ) C ls (mv θ δ) (K.plug (.val w)) ρt

/-- **`KappaRelends`**: the continuation re-lends at every re-making of the region. -/
def KappaRelends (K : Kont) (B : VTy) (C : CTy) (δ : LSub) (ρ : WRes) : Prop :=
  ∀ (c : Life) (θ : Restrat.Emb c), RelendsAt (ℍ := ℍ) θ K B C δ ρ

/-- **A typed segment re-lends at every re-making**: its context has a re-make hereditarily typed
at the moved reading, at which the segment, plugged with any answer related there, is related
there. -/
theorem kappa_relend {K : Kont} {Δ : LifeCtx} {Γ : Ctx VTy} {B : VTy} {C : CTy} {γ : List Val}
    (hK : TypedSeg K Δ Γ B C γ) {δ : LSub} {ρ : WRes} (hδ : Δ.Models δ)
    (hlive : Ctx.LiveWithin Γ γ) (hg : HTG (ℍ := ℍ) Γ δ γ ρ) {c : Life} (θ : Restrat.Emb c) :
    ∃ ρ', RemakeR θ ρ ρ' ∧ HTG (ℍ := ℍ) Γ (mv θ δ) γ ρ' ∧
      ∀ (ls : List SRec) (w : Val) (ρw ρt : WRes),
        vCE (ℍ := ℍ) none true B ls (mv θ δ) w ρw → ResU.CompS ρw ρ' ρt →
          cC (ℍ := ℍ) C ls (mv θ δ) (K.plug (.val w)) ρt := by
  obtain ⟨E, hE, hplug⟩ := hK
  obtain ⟨ρ', hR, hg'⟩ := htg_relend θ hg
  refine ⟨ρ', hR, hg', fun ls w ρw ρt hw hc => ?_⟩
  rw [hplug w]
  have hS : SemC Δ (⟨B, true⟩ :: Γ) E C := fundamentalC (ℍ := ℍ) hE
  refine hS (mv θ δ) (w :: γ) ls ρt ((θ.models_mapN_iff Δ δ).mpr hδ) (pure_sep_mk hlive ?_)
  unfold gSepC
  rw [if_pos rfl]
  exact ⟨ρw, ρ', hc, hw, htg_sound hg' ls⟩

/-- A typed segment over a hereditarily typed context satisfies `KappaRelends`. -/
theorem kappaRelends_of_typed {K : Kont} {Δ : LifeCtx} {Γ : Ctx VTy} {B : VTy} {C : CTy}
    {γ : List Val} (hK : TypedSeg K Δ Γ B C γ) {δ : LSub} {ρ : WRes} (hδ : Δ.Models δ)
    (hlive : Ctx.LiveWithin Γ γ) (hg : HTG (ℍ := ℍ) Γ δ γ ρ) :
    KappaRelends (ℍ := ℍ) K B C δ ρ := fun _ θ => by
  obtain ⟨ρ', hR, -, h⟩ := kappa_relend hK hδ hlive hg θ
  exact ⟨ρ', hR, h⟩

/-- **At the reading it was suspended at, a typed segment is related**: the identity re-making
leaves the reading where it was. The relation `contShare` gives the continuation at a stop is
this one. -/
theorem typedSeg_related {K : Kont} {Δ : LifeCtx} {Γ : Ctx VTy} {B : VTy} {C : CTy}
    {γ : List Val} (hK : TypedSeg K Δ Γ B C γ) {δ : LSub} {ρ : WRes} (hδ : Δ.Models δ)
    (hlive : Ctx.LiveWithin Γ γ) (hg : HTG (ℍ := ℍ) Γ δ γ ρ) (ls : List SRec) (w : Val)
    (ρw ρt : WRes) (hw : vCE (ℍ := ℍ) none true B ls δ w ρw) (hc : ResU.CompS ρw ρ ρt) :
    cC (ℍ := ℍ) C ls δ (K.plug (.val w)) ρt := by
  obtain ⟨E, hE, hplug⟩ := hK
  rw [hplug w]
  refine (fundamentalC (ℍ := ℍ) hE : SemC Δ (⟨B, true⟩ :: Γ) E C) δ (w :: γ) ls ρt
    hδ (pure_sep_mk hlive ?_)
  unfold gSepC
  rw [if_pos rfl]
  exact ⟨ρw, ρ, hc, hw, htg_sound hg ls⟩

end Law2

end
