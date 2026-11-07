import Core.Chain.RowFamK835N

/-!
# The loop at the typed tables  `[spec §14, §62]`

`docs/new-core/scope-835-tables.md` §9. `erwpK_iterateCI` at the world `KW`, at a row's table
(`tabNK`), every table premise discharged:

* **the tick's invariant along the tick's order** (`tabNK_tickInv`): the typed loop's invariant
  `𝒱⟦S⟧ ∧ ConsistentX` (`iterate_compatN`'s) at the stop's world is one at every world the tick's
  entry owes its continuation at. The order is `ExtR` at the share (`KW.OwedS.extR`), the state's
  resource being the whole share, along which `𝒱⟦S⟧` is kept (`vN_extR`); the view is one the
  order makes consistent with the share (`KW.OwedS.consistent`);
* **the tick's entry** (`tabNK_tick`): `Div`'s `tick` in the row (`Row.divB_find`), must-resume,
  its payload `()`, its answer *next* or *close*;
* **E5** (`tabNK_ctxClosed`) and the tables' closure in the index (`tabNK_downI`), at the worlds
  whose location typing is downward closed, which every owed world is.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Kont)

/-- **The loop's invariant along an entry's order, at the lender's tables**: a value of `A` at the
stop's world, consistent with its view, is one at every world the entry owes its continuation at,
at the same resource (the whole share). -/
theorem tabNK_tickInv {S : UInt32 → Prop} {F : CTy} {δ : LSub} {x : KW} {m i : UInt32}
    {en : OpEntK KW} (h : tabNK (ℍ := ℍ) S id F δ x m i = some en) {f : Life} {y : KW}
    {ρ : WRes} (hy : en.wk f y ρ) (A : VTy) {k : Nat} {s : Val}
    (hI : vN (ℍ := ℍ) A δ x.Θ k s ρ ∧ ConsistentX x.c ρ) :
    vN (ℍ := ℍ) A δ y.Θ k s ρ ∧ ConsistentX y.c ρ := by
  obtain ⟨_, _, _, _, _, rfl, -⟩ := tab_lookupNNK F h
  exact ⟨vN_extR A δ k s ρ (KW.OwedS.extR hy) hI.1, KW.OwedS.consistent hy⟩

/-- **`tick`'s entry in a row's table at `KW`**, with `erwpK_iterateCI`'s `htick` at the typed
invariant: must-resume, payload `()`, answer *next* or *close* holding nothing, the invariant
carried along its order (`tabNK_tickInv`). -/
theorem tabNK_tick (S : UInt32 → Prop) {Sg : Row} (hS : Row.divB Sg = true) (St Rt : VTy)
    (δ : LSub) (x : KW) :
    ∃ en, tabNK (ℍ := ℍ) S id (CTy.effOf Sg Rt) δ x divEff 0 = some en ∧ en.abort = false ∧
      en.q = .lin ∧ (∀ k ls, en.PA k ls Val.unit PMap.empty) ∧
      (∀ y k ls w (ρ : WRes), en.PB y k ls w ρ → (w = nextV ∨ w = closeV) ∧ ρ = PMap.empty) ∧
      ∀ fl' y k s ρ, en.wk fl' y ρ →
        (vN (ℍ := ℍ) St δ x.Θ k s ρ ∧ ConsistentX x.c ρ) →
        vN (ℍ := ℍ) St δ y.Θ k s ρ ∧ ConsistentX y.c ρ := by
  obtain ⟨o, hfo, hto⟩ := Row.divB_find hS
  obtain ⟨hoq, hoA, hoB⟩ := tickB_sig hto
  have hT : tabNK (ℍ := ℍ) S id (CTy.effOf Sg Rt) δ x divEff 0 = some ((rdKW id δ).ent
      S divEff o.q o.A o.B (finF (ℍ := ℍ) (rdKW id δ) ((rdKW id δ).sub S divEff) o.fin) x) := by
    rw [← tabF_KW, tabF_effOf_find, hfo]; rfl
  refine ⟨_, hT, by simp [RowRd.ent, hoq], hoq, fun k ls => ?_, fun y k ls w ρ hB => ?_,
    fun fl' y k s ρ hy hI => tabNK_tickInv hT hy St hI⟩
  · show vN (ℍ := ℍ) o.A δ x.Θ k Val.unit PMap.empty
    rw [hoA]; exact ⟨rfl, rfl⟩
  · have hB' : vN (ℍ := ℍ) o.B δ y.Θ k w ρ := hB.1
    rw [hoB] at hB'
    rcases hB' with ⟨v₁, rfl, rfl, rfl⟩ | ⟨v₂, rfl, rfl, rfl⟩
    · exact ⟨Or.inl rfl, rfl⟩
    · exact ⟨Or.inr rfl, rfl⟩

/-- **E14 at the typed tables** (`erwpK_iterateCI` at `KW`): the loop at a row holding `Div`, its
table the row's `tabNK`, the invariant `𝒱⟦S⟧ ∧ ConsistentX` read at a world. Every premise on the
tables is discharged: closure in the index (`tabNK_downI`), E5 at the loop's two contexts
(`tabNK_ctxClosed`), the tick (`tabNK_tick`); a post is at the run's own world (`KW.PostK`). The
turn, the close path and the answer's sum are `erwp_iterateCI`'s premises, read at every world
whose location typing is downward closed. -/
theorem erwpK_iterate_tabKW (S : UInt32 → Prop) {Sg : Row} (hS : Row.divB Sg = true)
    {St B R : VTy} {δ : LSub} {f : Val} {QL QR : KW → PostN} (hQL : ∀ y, (QL y).Down) (N : Nat)
    (hturn : ∀ y : KW, y.Θ.Down → ∀ k, k ≤ N → ∀ s ls ρ,
      vN (ℍ := ℍ) St δ y.Θ k s ρ ∧ ConsistentX y.c ρ →
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabNK (ℍ := ℍ) S id (CTy.effOf Sg (.sum B R)) δ z))
        (fun z => turnPostNI (fun k s ρ => vN (ℍ := ℍ) St δ z.Θ k s ρ ∧ ConsistentX z.c ρ) (QL z))
        y k ls (.app (.app (.val f) (.val s)) (.val nextV)) ρ)
    (hclose : ∀ y : KW, y.Θ.Down → ∀ k, k ≤ N → ∀ s ls ρ,
      vN (ℍ := ℍ) St δ y.Θ k s ρ ∧ ConsistentX y.c ρ →
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabNK (ℍ := ℍ) S id (CTy.effOf Sg (.sum B R)) δ z)) QR y k ls
        (obsCN f s) ρ)
    (hQLR : ∀ y k ls r ρ, QR y k ls r ρ → QL y k ls (Val.inj₂ r) ρ) :
    ∀ n, n ≤ N → ∀ x : KW, x.Θ.Down → ∀ s ls ρ,
      vN (ℍ := ℍ) St δ x.Θ n s ρ ∧ ConsistentX x.c ρ →
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabNK (ℍ := ℍ) S id (CTy.effOf Sg (.sum B R)) δ z)) QL x n ls
        (iterateE f s) ρ :=
  erwpK_iterateCI (V := KW.PostK) KW.postK_refl (fun _ _ _ h₁ h₂ => h₁.trans h₂)
    (Φ := fun z => z.Θ.view z.c) (Inv := fun z : KW => z.Θ.Down)
    (fun x hx => LocTy.view_down hx x.c) (fun _ _ h => by rw [h])
    (fun _ _ h hx => by rw [h]; exact hx) (fl := fun z => z.lo)
    (fun x => tabNK_downI S id _ δ x)
    (fun _ _ h => tabLe_postK (fun z => opTableK z.lo (tabNK (ℍ := ℍ) S id _ δ z)) h)
    (fun x => tabNK_ctxClosed S id _ δ (iterK f) (fun m => by simp [iterK, Kont.HasHnd])
      (by simp [iterK, Kont.Catches]) x)
    (fun x => tabNK_ctxClosed S id _ δ inrK inrK_plain.1 (inrK_plain.2 0) x) hQL
    (I := fun z k s ρ => vN (ℍ := ℍ) St δ z.Θ k s ρ ∧ ConsistentX z.c ρ)
    (fun _ _ _ _ _ hk h => ⟨vN_le hk h.1, h.2⟩)
    (fun x => tabNK_tick S hS St (.sum B R) δ x) N hturn hclose hQLR

end BoCa.Fig16.LogRel.Core.Chain.SI

end
