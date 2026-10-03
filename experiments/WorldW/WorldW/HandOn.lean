import WorldW.Wp

/-!
# WorldW — the resource core of a frame handed on at a stop (DESIGN §7, reading 2)

**World: resources, at the closures `Close` takes** (so at the W-draft's conjunct (37)).

DESIGN §7's reading 2: *`TabAt` (6.50) takes the place of the box at a hand-on stop; every
hand-on step is a printed lemma at a chosen split.* This file checks that reading for 6.64 and
6.65 at the resource level, on every path:

* `handOn64` (resume, 6.64). From the borrower's relativised `↭` between the closures of its start
  and of its stop, and the open-entry invariant's resource half at the start (`TabAt`, the exit
  defined), the same holds at the stop: `TabAt` (6.50), the view at the top level (6.29), the exit
  defined (6.38, with the split view ↦ `ρ⁺`, rest ↦ `ρ′`, `TabAt` off `ℓ` standing for H4). The
  lender's relativised `↭` holds with the frame closed on both sides (6.39).
* `exit64` (return, abortive stop, cancel's end, 6.64). At an end whose resource splits into a part
  in `Res_α` and an own-free rest (the box at a return, the closed argument at an abortive stop,
  the closed error at a cancel's end), the printed exit applies: 6.29, 6.38, 6.39.
* `handOn65` (every path, 6.65). 6.27 puts the lend's cell `mut(α, v′, χ′, Q̂)` at the top of the
  stop's closure with the same `α` and `Q̂`; 6.24 makes the exit defined; 6.28 (an iff) gives the
  lender's relativised `↭`; 6.50 keeps the rest above `α`.
* `handOn150` (resume, 6.150). 6.52 with the split `ρ′ := ∅`, `ρ⁺ :=` the stop's resource puts the
  image at the top of the stop's closure with its subtraction in `Res_β`; 6.59 gives the lender's
  relativised `↭` with the reborrow closed on both sides and the view kept.
* `anti_handOn_needs_invariant` (6.66). Closing an anti entry at a stop refolds its place, which
  needs `P̂` of the content at the stop; where `P̂` fails, no closure of the stop is `↭`-related to
  the start's.

These are the steps of the `OpenFrame*` and `OpenRecord150` probes that touch resources (DESIGN
§4.3, (ii)–(iv) and the value case; §4.7). They are not the probes: the probes also carry the frame
list, the record list and its tags, the payload's relation along the list, the tables and the
shares.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace WorldW
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

theorem single_del_self (l : BoCa.Loc) (ψ : CellU BoCa.Loc Val) :
    (ResU.single l ψ).del l = PMap.empty := by
  classical
  refine PMap.ext fun k => ?_
  by_cases hk : k = l
  · subst hk; rw [ResU.del_get_self]; rfl
  · rw [ResU.del_get_ne _ hk, single_get_none _ hk]; rfl

/-- Off `ℓ` the cells of a resource the table holds of are in `Res_α`. -/
theorem tabAt_del_inStratum {l : BoCa.Loc} {α : Life} {ρ : WRes} (h : GhostEnd.TabAt l α ρ) :
    (ρ.del l).InStratum α := by
  classical
  intro k ψ e
  by_cases hk : k = l
  · subst hk; rw [ResU.del_get_self] at e; exact absurd e (by simp)
  · rw [ResU.del_get_ne _ hk] at e; exact h.2 k ψ hk e

/-- The borrower's part beside the view is in `Res_α`: off `ℓ` by the table, and at `ℓ` empty,
since it is compatible with the owned form. -/
theorem rest_inStratum_of_tab {p : FrameRec} {α : Life}
    {hR : p.R.InStratum (LSet.singleton α).join} {ρs ρb W : WRes}
    (hW : ResU.CompS p.R (ResU.single p.le (CellU.ownOf p.v)) W)
    (hρs : ResU.CompS ρb (ResU.single p.le (CellU.immOf (LSet.singleton α) p.v p.R hR)) ρs)
    (h1 : ResU.Hash ρb W) (htab : GhostEnd.TabAt p.le α ρs) : ρb.InStratum α := by
  obtain ⟨-, X, hX, -⟩ := h1
  have hWl : W.get p.le = some (CellU.ownOf p.v) :=
    compS_get_of_right_nonimm hW (ResU.single_get_self _ _) (kind_ownOf_ne p.v)
  have hbl : ρb.get p.le = none := compS_left_none_of_right hX hWl (kind_ownOf_ne p.v)
  intro k ψ e
  have hk : k ≠ p.le := by rintro rfl; rw [hbl] at e; exact absurd e (by simp)
  refine htab.2 k ψ hk ?_
  rw [compS_get_left hρs (single_get_none _ hk)]; exact e

/-- **`exit64`: 6.64's exit at an end** whose resource splits into a part in `Res_α` and an
own-free rest: the exit is defined there (6.29, 6.38), and the lender's relativised `↭` holds with
the frame closed on both sides (6.39). -/
theorem exit64 {p : FrameRec} {α : Life} {hR : p.R.InStratum (LSet.singleton α).join}
    {ρs ρb W πs ρ' ρp : WRes}
    (hW : ResU.CompS p.R (ResU.single p.le (CellU.ownOf p.v)) W)
    (hρs : ResU.CompS ρb (ResU.single p.le (CellU.immOf (LSet.singleton α) p.v p.R hR)) ρs)
    (h1 : ResU.Hash ρb W) (htab : GhostEnd.TabAt p.le α ρs) (hu : ResU.UpdV ρs πs)
    (hπ : ResU.CompS ρ' ρp πs) (h4 : ρ'.InStratum α) (hown : NoOwn ρp) :
    ∃ G, ResU.CompS ρ' (ρp.del p.le) G ∧ ResU.Hash G W ∧
      ResU.CompS G (ResU.single p.le (CellU.immOf (LSet.singleton α) p.v p.R hR)) πs ∧
      ∃ ρo πo, ResU.CompS ρb W ρo ∧ ResU.CompS G W πo ∧ ResU.UpdV ρo πo := by
  have hb := rest_inStratum_of_tab hW hρs h1 htab
  have h2 : ResU.Hash ρ' ρp := ⟨hπ.1, πs, hπ, hu.2.2⟩
  obtain ⟨G, hG, hGW⟩ := ResU.six38 hW h1 h2 hb h4 hown hρs hπ hu
  obtain ⟨hGs, -, hGc⟩ := ResU.six38_steps_one_two hW h1 h2 hb h4 hρs hπ hu
  cases ResU.CompS.functional hGs hG
  obtain ⟨ρo, πo, hρo, hπo, huo⟩ :=
    ResU.six39 (ResU.CompS.comm hW) h1 hGW hρs hGc hu
  exact ⟨_, hG, hGW, hGc, ρo, πo, hρo, hπo, huo⟩

/-- **`handOn64`: 6.64's frame handed on at a resuming stop.** The table is kept (6.50), the view
is at the top of the stop's closure (6.29), the exit is defined there (6.38 with the split
view ↦ `ρ⁺`, rest ↦ `ρ′`, the table off `ℓ` standing for H4), and the lender's relativised `↭`
holds with the frame closed on both sides (6.39). So the open-entry invariant's resource half
holds again at the stop. -/
theorem handOn64 {p : FrameRec} {α : Life} {hR : p.R.InStratum (LSet.singleton α).join}
    {ρs πs ρb W : WRes}
    (hW : ResU.CompS p.R (ResU.single p.le (CellU.ownOf p.v)) W)
    (hρs : ResU.CompS ρb (ResU.single p.le (CellU.immOf (LSet.singleton α) p.v p.R hR)) ρs)
    (h1 : ResU.Hash ρb W) (htab : GhostEnd.TabAt p.le α ρs) (hu : ResU.UpdV ρs πs) :
    GhostEnd.TabAt p.le α πs ∧
    ResU.CompS (πs.del p.le) (ResU.single p.le (CellU.immOf (LSet.singleton α) p.v p.R hR)) πs ∧
    ResU.Hash (πs.del p.le) W ∧
    ∃ ρo πo, ResU.CompS ρb W ρo ∧ ResU.CompS (πs.del p.le) W πo ∧ ResU.UpdV ρo πo := by
  have htab' := GhostEnd.tabAt_updV htab hu
  have hb := rest_inStratum_of_tab hW hρs h1 htab
  have hsplit := ResU.six29 hb hW h1 hρs hu
  obtain ⟨G, hG, hGW, -, ρo, πo, hρo, hπo, huo⟩ :=
    exit64 hW hρs h1 htab hu hsplit (tabAt_del_inStratum htab')
      (ResU.restrict_single_other (by simp))
  rw [single_del_self] at hG
  cases ResU.CompS.functional hG (ResU.comp_empty_right _)
  exact ⟨htab', hsplit, hGW, ρo, πo, hρo, hπo, huo⟩

/-- **`handOn65`: 6.65's lend on every path.** 6.27 puts the lend's cell at the top of the stop's
closure with the same lifetime and predicate; 6.24 makes the exit defined; 6.28 gives the lender's
relativised `↭` with the lend closed on both sides; 6.50 keeps the rest above `α`. -/
theorem handOn65 {l : BoCa.Loc} {α : Life} {v : Val} {χ : WRes} {hχ : χ.InStratum α}
    {Q : Val → SPropS BoCa.Loc Val α} {hw : Q v ⟨χ, hχ⟩} {ρr ρs πs : WRes}
    (hρs : ResU.CompS ρr (ResU.single l (CellU.mutOf α v χ hχ Q hw)) ρs) (hr : ρr.InStratum α)
    (hu : ResU.UpdV ρs πs) :
    (πs.del l).InStratum α ∧
    ∃ (v' : Val) (χ' : WRes) (h' : χ'.InStratum α) (hw' : Q v' ⟨χ', h'⟩),
      ResU.CompS (πs.del l) (ResU.single l (CellU.mutOf α v' χ' h' Q hw')) πs ∧
      ∃ W W' ρo πo, ResU.CompS χ (ResU.single l (CellU.ownOf v)) W ∧
        ResU.CompS χ' (ResU.single l (CellU.ownOf v')) W' ∧
        ResU.CompS ρr W ρo ∧ ResU.CompS (πs.del l) W' πo ∧ ResU.UpdV ρo πo := by
  classical
  -- the table at `(l, α)` holds at the start, so at the stop (6.50)
  have hrl : ρr.get l = none :=
    compS_left_none_of_right hρs (ResU.single_get_self _ _) kind_mutOf_ne
  have htab : GhostEnd.TabAt l α ρs := by
    refine (GhostEnd.tabAt_comp (ResU.CompS.comm hρs)).mpr ⟨?_, GhostEnd.tabAt_of_inStratum hr⟩
    refine ⟨fun k ψ e => ?_, fun k ψ hk e => absurd e (by rw [single_get_none _ hk]; simp)⟩
    by_cases hk : k = l
    · subst hk; rw [ResU.single_get_self] at e; cases Option.some.inj e
      exact GhostEnd.down_lt α
    · rw [single_get_none _ hk] at e; exact absurd e (by simp)
  have htab' := GhostEnd.tabAt_updV htab hu
  obtain ⟨v', χ', h', hw', hsplit⟩ := ResU.six27 hr hρs hu
  have hvs : ResU.Valid ρs := hu.2.1
  have hvπ : ResU.Valid πs := hu.2.2
  obtain ⟨W, hW⟩ := ResU.compS_own_of_valid_mut (ResU.Valid.split hρs hvs).2
  obtain ⟨W', hW'⟩ := ResU.compS_own_of_valid_mut (ResU.Valid.split hsplit hvπ).2
  have hH : ResU.Hash ρr W := (ResU.six24 hW).mp ⟨hρs.1, ρs, hρs, hvs⟩
  have hH' : ResU.Hash (πs.del l) W' := (ResU.six24 hW').mp ⟨hsplit.1, πs, hsplit, hvπ⟩
  obtain ⟨-, ρo, hρo, hvo⟩ := hH
  obtain ⟨-, πo, hπo, hvπo⟩ := hH'
  have hupd := (ResU.six28 hW hW' hρs hsplit hρo hπo hvs hvπ hvo hvπo).mp hu.1
  exact ⟨tabAt_del_inStratum htab', v', χ', h', hw', hsplit, W, W', ρo, πo, hW, hW', hρo, hπo,
    ⟨hupd, hvo, hvπo⟩⟩

/-! ### 6.66: the refold at a stop

`[TR]` 6.66 asks the body to hand back `ℓ ↦ v″ ⋆ P̂(v″)` when it returns (H20). Under the draft's
conjunct (37) a stop that hands an anti entry on must also close it in `Close τ′ π πc`, which
refolds the place: so the content at the stop must satisfy `P̂`. `anti_handOn_needs_invariant`
states it at the lender's (37): when the place holds `own(w)` and `P̂(w)` holds of no resource, no
closure of the stop is `↭`-related to the start's closure, whatever list the stop hands on. -/

/-- **An anti place whose content breaks its invariant cannot be refolded by any closure**: no
closure carries `mut(β, _, _, P̂)` there. -/
theorem anti_unclosable {τ : List OEnt} {π πc F : WRes} {l : BoCa.Loc} {w : Val} {β : Life}
    {P : Val → SPropS BoCa.Loc Val β} (hπ : π.get l = some (CellU.ownOf w))
    (hP : ∀ ρ, ¬ P w ρ) (hc : Close τ π πc) (hF : ResU.Flat πc F) :
    ∀ v χ h hw, F.get l ≠ some (CellU.mutOf β v χ h P hw) := by
  intro v χ h hw hFl
  obtain ⟨U, A, -, hr, -, -, -, hown⟩ :=
    close_pair hc hc (.nil π) (.nil π) rfl (fun _ h => absurd h List.not_mem_nil)
      (fun _ h => absurd h List.not_mem_nil)
  have hUl := hown l w hπ
  obtain ⟨FU, hFU⟩ := refolds_valid_start hr ⟨F, hF⟩
  have hFUl : FU.get l = some (CellU.ownOf w) := ResU.flat_get_of_ne_imm hFU hUl (kind_ownOf_ne w)
  obtain ⟨hoff, hat⟩ := refolds_flat hr ⟨FU, hFU⟩ hFU hF
  by_cases hl : ∃ f ∈ A, f.l = l
  · obtain ⟨⟨fl, fβ, fP, fρ⟩, hf, rfl⟩ := hl
    obtain ⟨v', χ', h', hw', hFf, hFUf⟩ := hat _ hf
    simp only at hFf hFUf
    rw [hFUl] at hFUf
    have hvw : w = v' := by simpa [CellU.ownOf] using Option.some.inj hFUf
    rw [hFl] at hFf
    have he := Option.some.inj hFf
    obtain rfl : β = fβ := CellU.mutOf_at he
    obtain ⟨rfl, -, -⟩ := CellU.mutOf_inj he
    exact hP _ (hvw ▸ hw)
  · rw [hoff l (fun f hf e => hl ⟨f, hf, e⟩), hFUl] at hFl
    exact CellU.ownOf_ne_mutOf (Option.some.inj hFl)

/-- **The lender's relativised `↭` fails at a stop where an anti entry's content breaks its
invariant**, whatever list the stop hands on: the start's closure carries the refolded
`mut(β, _, _, P̂)` at the place, and no closure of the stop does. -/
theorem anti_handOn_needs_invariant {τi τ' : List OEnt} {l : BoCa.Loc} {α β : Life} {T : VTy}
    {δ : LSub} {P : Val → SPropS BoCa.Loc Val β} {ρ ρc π πc : WRes} {w : Val}
    (hρ : Close (τi ++ [.anti l α β T δ P]) ρ ρc) (hv : ResU.Valid ρc)
    (hπ : π.get l = some (CellU.ownOf w)) (hP : ∀ ρ', ¬ P w ρ') (hc : Close τ' π πc) :
    ¬ ResU.UpdV ρc πc := by
  intro hu
  obtain ⟨Fρ, hFρ⟩ := hv
  have hlen : τi.length < (τi ++ [OEnt.anti l α β T δ P]).length := by simp
  obtain ⟨u, ⟨χ, h, hw, hFl⟩, -⟩ := (close_flat_agree hρ hρ hFρ hFρ).2 τi.length hlen l α β T δ P
    (by simp) (by simp)
  obtain ⟨Fπ, hFπ⟩ := hu.2.2
  obtain ⟨u', χ', h', hw', hπl⟩ :=
    (hu.1.2 l β P).mp ⟨u, χ, h, hw, (ResU.flatAt_iff hFρ _ _).mpr hFl⟩
  exact anti_unclosable hπ hP hc hFπ u' χ' h' hw' ((ResU.flatAt_iff hFπ _ _).mp hπl)

/-! ### 6.150: a reborrow handed on at a stop -/

/-- A reborrow image restricted to the source's exclusive locations is a reborrow image too:
`reb_β`'s family restricted to those locations. -/
theorem reb_restrict {β : Life} {σR χ : WRes} (h : ResU.Reb β σR χ) :
    ResU.Reb β σR (χ.restrictDom σR.exclPart) := by
  classical
  obtain ⟨hs, π, b, hdom, hbig, hle, hat⟩ := h
  let q : BoCa.Loc × WRes → Bool := fun lp => (σR.exclPart.get lp.1).isSome
  have hget : ∀ l, (χ.restrictDom σR.exclPart).get l =
      if (σR.exclPart.get l).isSome then χ.get l else none := fun _ => rfl
  obtain ⟨b', hbig', hle'⟩ :=
    BigComp.leS_of_sublist (List.Sublist.map _ (List.filter_sublist (p := q) (l := π))) hbig
  refine ⟨hs, π.filter q, b', ⟨?_, fun l => ?_⟩, hbig', ResU.Le.trans hle' hle,
    fun l p hlp => ?_⟩
  · exact (List.Sublist.map _ (List.filter_sublist (p := q) (l := π))).nodup hdom.1
  · rw [hget]
    constructor
    · intro hl
      obtain ⟨⟨l', p⟩, hlp, rfl⟩ := List.mem_map.mp hl
      obtain ⟨hlp, hq⟩ := List.mem_filter.mp hlp
      simp only [q] at hq
      rw [if_pos hq]
      exact (hdom.2 _).mp (List.mem_map_of_mem (f := Prod.fst) hlp)
    · rintro ⟨ψ, hψ⟩
      by_cases hq : (σR.exclPart.get l).isSome
      · rw [if_pos hq] at hψ
        obtain ⟨⟨l', p⟩, hlp, e⟩ := List.mem_map.mp ((hdom.2 l).mpr ⟨ψ, hψ⟩)
        simp only at e
        subst e
        exact List.mem_map_of_mem (f := Prod.fst) (List.mem_filter.mpr ⟨hlp, by simpa [q] using hq⟩)
      · rw [if_neg hq] at hψ; exact absurd hψ (by simp)
  · obtain ⟨hlp, hq⟩ := List.mem_filter.mp hlp
    simp only [q] at hq
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hat l p hlp
    refine ⟨h₁, fun v hv => ?_, fun b' v χ' hb P hw hv => ?_, fun s' v χ' h hv => ?_⟩
    · rw [hget, if_pos hq]; exact h₂ v hv
    · rw [hget, if_pos hq]; exact h₃ b' v χ' hb P hw hv
    · rw [hget, if_pos hq]; exact h₄ s' v χ' h hv

theorem restrictDom_idem (χ σ : WRes) : (χ.restrictDom σ).restrictDom σ = χ.restrictDom σ := by
  classical
  refine PMap.ext fun l => ?_
  show (if (σ.get l).isSome then (χ.restrictDom σ).get l else none) = (χ.restrictDom σ).get l
  by_cases h : (σ.get l).isSome
  · rw [if_pos h]
  · rw [if_neg h]; show none = (if (σ.get l).isSome then χ.get l else none); rw [if_neg h]

/-- **`handOn150`: a 6.150 record handed on at a stop** (reading 2 for 6.150). The borrower holds
the image beside a part `Xr` in `Res_β` and runs beside the view. At the stop, 6.52 (split
`ρ′ := ∅`, `ρ⁺ :=` the stop's resource) puts the image at the top of the stop's closure, its
subtraction in `Res_β` (the open-entry invariant's strata again), and 6.59 gives the lender's
relativised `↭` with the reborrow closed on both sides and the view kept. -/
theorem handOn150 {l : BoCa.Loc} {s : LSet} {w : Val} {σR : WRes} {hs : σR.InStratum s.join}
    {β : Life} {χ X Xr πs : WRes} (hreb : ResU.Reb β σR χ)
    (hX : ResU.CompS Xr (χ.restrictDom σR.exclPart) X) (hXr : Xr.InStratum β)
    (hh1 : ResU.Hash Xr (ResU.single l (CellU.immOf s w σR hs))) (hu : ResU.UpdV X πs)
    (hh2 : ResU.Hash πs (ResU.single l (CellU.immOf s w σR hs))) :
    ∃ χ', ResU.SubKeep πs (χ.restrictDom σR.exclPart) χ' ∧
      ResU.CompS χ' (χ.restrictDom σR.exclPart) πs ∧ χ'.InStratum β ∧
      ∃ Xi Y, ResU.CompS (ResU.single l (CellU.immOf s w σR hs)) Xr Xi ∧
        ResU.CompS χ' (ResU.single l (CellU.immOf s w σR hs)) Y ∧ ResU.UpdV Xi Y := by
  have hreb' := reb_restrict hreb
  have hce : ResU.CompS (χ.restrictDom σR.exclPart) Xr X := ResU.CompS.comm hX
  have hcp : ResU.CompS PMap.empty πs πs := compS_empty_left πs
  have hs0 : ResU.InStratum β (PMap.empty : WRes) := ResU.inStratum_empty β
  obtain ⟨χ', hsk, hcχ', hχ'⟩ := ResU.six52_keep hreb' hce hcp hu hXr hs0
  rw [restrictDom_idem] at hsk hcχ'
  obtain ⟨-, Xi, hXi, hvXi⟩ := hh1
  obtain ⟨-, Z, hZ, hvZ⟩ := hh2
  -- `χ′ ● view` is a part of `πs ● view`
  obtain ⟨Y', hY', hY'Z⟩ := compS_exch hcχ' hZ
  have hvY' : ResU.Valid Y' := (ResU.Valid.split hY'Z hvZ).1
  obtain ⟨σX, hσX⟩ := hvXi
  obtain ⟨σY, hσY⟩ := hvY'
  have hupd := ResU.six59 hreb' hce hcp hu hXr hs0
    ⟨hXi.1, Xi, hXi, ⟨σX, hσX⟩⟩ ⟨hZ.1, Z, hZ, hvZ⟩
    (by rw [restrictDom_idem]; exact hsk) (ResU.CompS.comm hXi)
    ⟨χ', compS_empty_left χ', hY'⟩ hσX hσY
  exact ⟨χ', hsk, hcχ', hχ', Xi, Y', ResU.CompS.comm hXi, hY',
    ⟨hupd, ⟨σX, hσX⟩, ⟨σY, hσY⟩⟩⟩

end WorldW

end
