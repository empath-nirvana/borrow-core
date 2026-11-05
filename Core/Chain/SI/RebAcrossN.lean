import Core.Chain.SI.RebResumeN

/-!
# 6.150 across a stop: the exit, and what the re-entry needs of the frame

## The exit: `RebEndRec` from the entry world, through `↭`

At a reborrow's end (`TWN.rebEnd`) the world is `ρ_f ● Y`, `Y` the lender's resource after
6.52's split; the entry world before the image was added is `ρ_f ● ρ`, `ρ` the lender's resource
before. 6.59 gives `ρ ↭ Y` and 6.48 (`updVN_frame`) `ρ_f ● ρ ↭ ρ_f ● Y`. The `imm` clause of `↭`
is printed and symmetric (`updImm_symm`): the `imm` views of the two aliasable walks are the same
cells (`updImm_ag_imm_eq`, the `imm` branch of `ResU.upd_ag_eq_of_ne_own`). `NestLife` reads only
`imm` views, so it passes from the entry world, a `TWN` world (`TI`), to the exit world
(`nestLife_of_updImm`), and `RebEndRec` with it (`rebEndRec_of_updImm`). No stratum of the frame
is read: the frame may hold cells shorter than `β`, as at a resume inside a handler's lend.

## The re-entry: the image must agree with the resume frame

Re-entering at the resume with the image `χ` chosen at the first entry adds `χ` to the resume
world. `[TR]` 6.55 makes that defined when the frame's views at the escrow's `own` cells carry
`χ`'s witnesses (`EscrowAgree`). At the first entry the chooser picks `χ` to agree with the frame
there (`rebChooseO_top`: a joint image of the views present, relabelled, or the handed one if
there is none). Across the stop the fold removes `χ`'s views at those cells (the `imm` clause of
`↭` forbids keeping them), so nothing in the world records `χ`'s witnesses while the continuation
is stored. `RebReentryAgreeN` is the agreement the re-entry needs at every resume world.
`reb_witness_choice` shows the witnesses are a choice: two images of one escrow at one `β`, both
of the shape a `ref (thunk C)` reborrow asks for, whose cells at the root are not compatible.

`not_rebReentryAgreeN` (`SI/RebAgreeCex.lean`) refutes `RebReentryAgreeN` at a configuration
`TWN` reaches: the resume world holds the record's cell and an image of the other choice, made
by `TWN.reb` at the same records and tags.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar)

/-! ### The exit -/

/-- `NestLife` passes across the `imm` clause of `↭`: it reads only `imm` views, and those are
the same cells in the two aliasable walks. -/
theorem nestLife_of_updImm {W₀ W' : WRes} {r : FrameRec} (hv₀ : ResU.Valid W₀)
    (hv' : ResU.Valid W') (hu : ResU.UpdImm W₀ W') (hN : NestLife W₀ r) : NestLife W' r := by
  obtain ⟨σ₀, e₀, a₀, he₀, ha₀, hc₀⟩ := hv₀
  obtain ⟨σ', e', a', he', ha', hc'⟩ := hv'
  intro l₀ m S u hc a ha ψ s e hs x hx
  rw [AgW.functional ha ha'] at e ⊢
  have e₀ : a₀.get m = some ψ :=
    updImm_ag_imm_eq (updImm_symm hu) he' ha' hc' he₀ ha₀ hc₀ e (CellU.kind_of_lsOf hs)
  obtain ⟨ζ, t, y, eζ, ht, hy, hxy⟩ := hN l₀ m S u hc a₀ ha₀ ψ s e₀ hs x hx
  exact ⟨ζ, t, y, updImm_ag_imm_eq hu he₀ ha₀ hc₀ he' ha' hc' eζ (CellU.kind_of_lsOf ht), ht, hy,
    hxy⟩

/-- `NestLife` at every record gives the chain-positions premise of `rebEnd`. -/
theorem rebEndRec_of_nestLife {W' : WRes} {rs : List FrameRec} (h : ∀ r ∈ rs, NestLife W' r)
    (w₀ : WRes) (β : Life) : RebEndRec W' rs w₀ β :=
  fun r hr l₀ m S u hc _ a' ha' ψ s e hs x hx _ => h r hr l₀ m S u hc a' ha' ψ s e hs x hx

/-- **The exit's premise from the entry world.** A `TWN` world `W₀` and a valid `W′` related by
the `imm` clause of `↭` (6.59 then 6.48 at a reborrow's end) give `RebEndRec W′` at every escrow
and lifetime, whatever the frame holds. -/
theorem rebEndRec_of_updImm {W₀ W' : WRes} {ps rs : List FrameRec} (hT : TWN W₀ ps rs)
    (hv' : ResU.Valid W') (hu : ResU.UpdImm W₀ W') (w₀ : WRes) (β : Life) :
    RebEndRec W' rs w₀ β :=
  rebEndRec_of_nestLife
    (fun r hr => nestLife_of_updImm hT.valid hv' hu (hT.inv.2.2.2.2.1 r hr)) w₀ β


/-! ### The re-entry -/

/-- **The agreement the re-entry needs.** An image `χ` of a record's escrow at `β`, chosen at a
first entry, composes with every later typed, tagged world at the same records that holds the
record's cell: the frame's views at the escrow's `own` cells carry `χ`'s witnesses
(`EscrowAgree`, the input `[TR]` 6.55 asks for). -/
def RebReentryAgreeN : Prop :=
  ∀ (W₀ W : WRes) (ps₀ ps : List FrameRec) (ls ls' : List SRec) (r : FrameRec) (s : LSet)
    (hs : r.R.InStratum s.join) (χ : WRes) (β : Life) (x : LifeVar),
    TWN W₀ ps₀ (rsOf ls) → Tagged W₀ ps₀ ls → W₀.InStratum β → r ∈ rsOf ls →
    W₀.get r.le = some (CellU.immOf s r.v r.R hs) →
    ResU.Reb β r.R χ → vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v χ →
    (∀ a, AgW W₀ a → EscrowAgree r.R χ a) →
    TWN W ps (rsOf ls') → Tagged W ps ls' → (∀ y, y ∈ ls' ↔ y ∈ ls) →
    W.get r.le = some (CellU.immOf s r.v r.R hs) →
    ∀ a, AgW W a → EscrowAgree r.R χ a

theorem single_del_self (l : Loc) (ψ : CellU Loc Val) : (ResU.single l ψ).del l = PMap.empty := by
  refine PMap.ext fun k => ?_
  by_cases hk : k = l
  · subst hk; rw [ResU.del_get_self, PMap.empty_get]
  · rw [ResU.del_get_ne _ hk, ResU.single_get_ne ψ hk, PMap.empty_get]

theorem pair_del_left {l m : Loc} {ψ φ : CellU Loc Val} {R : WRes} (hlm : m ≠ l)
    (hR : ResU.CompS (ResU.single l ψ) (ResU.single m φ) R) : R.del l = ResU.single m φ := by
  refine PMap.ext fun k => ?_
  by_cases hk : k = l
  · subst hk; rw [ResU.del_get_self, ResU.single_get_ne φ (Ne.symm hlm)]
  · rw [ResU.del_get_ne _ hk, ← ResU.Comp.get_of_left_none hR (ResU.single_get_ne ψ hk)]

theorem pair_get_left {l m : Loc} {v u : Val} {R : WRes}
    (hR : ResU.CompS (ResU.single l (CellU.ownOf v)) (ResU.single m (CellU.ownOf u)) R) :
    R.get l = some (CellU.ownOf v) :=
  (ResU.CompS.get_left_of_ne_imm hR (ResU.single_get_self _ _) (by simp)).2

/-- An image at `β` of the escrow `ℓ ↦ own(v) ● m ↦ own(u)` that takes the piece `p` at `ℓ`. -/
theorem reb_pair_at {l m : Loc} {v u : Val} {R p w : WRes} {β : Life}
    (hR : ResU.CompS (ResU.single l (CellU.ownOf v)) (ResU.single m (CellU.ownOf u)) R)
    (hpl : p.get l = some (CellU.ownOf v)) (hpR : ResU.Le p R) (hpw : p.del l = w)
    (h : w.InStratum (LSet.singleton β).join) :
    ResU.Reb β R (ResU.single l (CellU.immOf (LSet.singleton β) v w h)) := by
  subst hpw
  have hRl := pair_get_left hR
  refine ⟨ResU.CompS.inStratum hR (ResU.inStratum_single l (by simp))
      (ResU.inStratum_single m (by simp)), [(l, p)], p, ⟨by simp, fun k => ?_⟩,
    BigComp.cons BigComp.nil (ResU.comp_empty_right p), hpR, fun k q hkq => ?_⟩
  · constructor
    · intro hk; simp only [List.map_cons, List.map_nil, List.mem_singleton] at hk
      subst hk; exact ⟨_, ResU.single_get_self _ _⟩
    · rintro ⟨ψ, e⟩
      by_cases hk : k = l
      · simp [hk]
      · rw [ResU.single_get_ne _ hk] at e; cases e
  · simp only [List.mem_singleton, Prod.mk.injEq] at hkq
    obtain ⟨rfl, rfl⟩ := hkq
    refine ⟨⟨_, hpl⟩, fun v' e => ?_, fun b v' χ hb P hw e => ?_, fun s v' χ h' e => ?_⟩
    · rw [hRl] at e; cases Option.some.inj e
      exact ⟨h, ResU.single_get_self _ _⟩
    · rw [hRl] at e; cases e
    · rw [hRl] at e; cases e

/-- **The witnesses of an image are a choice.** The escrow `ℓ ↦ own(v) ● m ↦ own(u)` of a
`ref (thunk C)` record has two images at one `β`, both of the shape the reborrow asks for: one
takes the piece `ℓ ↦ own(v)` at the root (witness `∅`), the other the whole escrow (witness
`m ↦ own(u)`). Their cells at the root are not compatible, so no world holds both. -/
theorem reb_witness_choice {l m : Loc} (hlm : m ≠ l) (v u : Val) (β : Life)
    (C : CTy) (δ : BoCa.Lifetime.LSub) (x : LifeVar) :
    ∃ R χA χB : WRes, vShape (.ref (.thunk C)) δ (.loc l) R ∧
      ResU.Reb β R χA ∧ ResU.Reb β R χB ∧
      vShape ((VTy.ref (.thunk C)).immReborrow (.var x)) (δ.extend x β) (.loc l) χA ∧
      vShape ((VTy.ref (.thunk C)).immReborrow (.var x)) (δ.extend x β) (.loc l) χB ∧
      ¬ ResU.CompatS χA χB := by
  obtain ⟨R, hR⟩ := (ResU.compS_defined_iff (ResU.single l (CellU.ownOf v))
    (ResU.single m (CellU.ownOf u))).mpr
    (compatS_single_of_get_none (ResU.single_get_ne _ hlm))
  have hRl := pair_get_left hR
  -- the two pieces at the root
  have hA0 : ((ResU.single l (CellU.ownOf v)).del l : WRes).InStratum (LSet.singleton β).join := by
    rw [single_del_self]; exact fun _ _ e => by rw [PMap.empty_get] at e; cases e
  have hB0 : (R.del l).InStratum (LSet.singleton β).join := by
    rw [pair_del_left hlm hR]; exact ResU.inStratum_single m (by simp)
  have hrebA := reb_pair_at hR (ResU.single_get_self _ _) ⟨_, hR⟩ rfl hA0
  have hrebB := reb_pair_at hR hRl ⟨_, ResU.comp_empty_right R⟩ rfl hB0
  have shapeOf : ∀ (w : WRes) (h : w.InStratum (LSet.singleton β).join),
      vShape ((VTy.ref (.thunk C)).immReborrow (.var x)) (δ.extend x β) (.loc l)
        (ResU.single l (CellU.immOf (LSet.singleton β) v w h)) := by
    intro w h
    refine ⟨β, ?_, l, pure_sep_mk rfl ⟨LSet.singleton β, v, w, h, rfl, trivial, le_refl _⟩⟩
    simp [BoCa.Lifetime.Life.interp, find?_extend_self]
    rfl
  refine ⟨R, _, _, ⟨l, v, pure_sep_mk rfl ⟨_, _, hR, rfl, trivial⟩⟩, hrebA, hrebB,
    shapeOf _ hA0, shapeOf _ hB0, fun hc => ?_⟩
  obtain ⟨s₁, s₂, v', ρ, h₁, h₂, e₁, e₂⟩ :=
    hc l _ _ (ResU.single_get_self _ _) (ResU.single_get_self _ _)
  have w₁ := (CellU.immOf_inj e₁).2.2
  have w₂ := (CellU.immOf_inj e₂).2.2
  rw [single_del_self] at w₁
  rw [pair_del_left hlm hR] at w₂
  have hm := congrArg (fun ρ : WRes => ρ.get m) (w₁.trans w₂.symm)
  simp only [PMap.empty_get, ResU.single_get_self] at hm
  cases hm

end BoCa.Fig16.LogRel.Core.Chain.SI

end
