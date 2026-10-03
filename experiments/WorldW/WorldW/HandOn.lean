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

These are the steps of `OpenFrame64`/`OpenFrame65` that touch resources (DESIGN §4.3, (ii)–(iv)
and the value case). They are not the probes: the probes also carry the frame list, the record
list and its tags, the payload's relation along the list, the tables and the shares.
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

end WorldW

end
