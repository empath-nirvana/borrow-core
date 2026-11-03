import Core.TreePoolSpawn

/-!
# Interleaved tasks holding lends across parks, through `PoolSchedAdequacyT`  `[spec §62]`

Closed programs run under the scheduler `HS` (`Core/TreePoolSpawn.lean`), each safe and
leak-free through the general headline `poolSchedAdequacyT`, every premise discharged.

**The loan task** `L = let a = alloc () in ubind (λ_. free a, λ_. free a) (park ())`. After the
allocation it opens a lend of `a` (`twp_lendOpen`), owning the lend's record and holding the lend
cell, a view of `a` (`viewRes α a`, which is its own copy: `viewRes_dup`); it parks holding the
view, its record open across the park. Resumed, `ubind` runs `N`: the view is merged back, the lend
ended (`twp_lendEnd`, at the resumer's guarantee that the frame holds nothing at `a`) and `a` freed.
Cancelled, `ubind` runs the finaliser `D` the same way, and the cancel answers `()`. `LC` is the
same task whose finaliser parks again (inside its own `ubind`) before ending the lend.

**The tests.**
* `progLoan`: the root spawns `B = L` and runs `L` itself. Under `HS`: B opens its lend and parks;
  the root resumes, opens its own lend and parks holding its view; B resumes, ends its lend (open
  since before the root parked) and finishes; the root resumes, merges its view, ends its lend and
  finishes.
* `progCancel`: the root spawns `C = park (); cancel ()` and runs `LC`. C parks; the root opens its
  lend and parks holding its view; C cancels the root (`poolAns_cancelSnd`, so `poolAns_cancel`);
  the root's finaliser parks again (C resumes and finishes), is resumed and ends the lend.
* `progDepth3`: the root spawns two `L`s and runs `L`; when the root parks, three tasks each hold a
  lend open across a park.

The safety statements quantify over every interleaving `HS` performs; the traces above are what
`HS`'s policy does with these programs.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.SchedProgs.SpawnProgs
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.Tree.Wp.SchedProgs.Park
open BoCa.Fig16.Tree.Wp.SchedProgs.Stack
open BoCa.Fig16.Tree.Wp.SchedProgs.Spawn
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE opPayload hndE hndVal capTag clauseAt ccatchE raiseE
  cancelVal freeE)

/-! ### Frames and pieces -/

def ccK : Kont := .appR (.prim .ccatch) .hole
def cfK2 : Kont := .appR (.prim .ccatch) (.appR (.app (.prim .cfin) (cancelVal none).1) .hole)
def ubK (N D : Val) : Kont := .appR (.app (.prim .ubind) (Val.pair N D).1) .hole

/-- `λ_. free ℓ`. -/
def Nf (l : BoCa.Loc) : Val := Val.lam (freeE (.val (Val.loc l)))
def parkE : Expr := performE (.val (opPayload nP 0 Val.unit))
def cancelE : Expr := performE (.val (opPayload nP 2 Val.unit))
def spawnE (th : Val) : Expr := performE (.val (opPayload nP 1 th))

/-- A post whose answers do not read the index, at a table whose payloads do not either. -/
theorem post_down {T : OpTabT}
    (hTd : ∀ m i en, T m i = some en → ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ)
    {Ψ : ContT} {F : TFrame} : (cerwpPostT (opTableT T) QS Ψ F).Down :=
  cerwpPostT_down QB_down hTd

theorem TS_down : ∀ m i en, TS (ℍ := ℍ) m i = some en →
    ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ := by
  intro m i en h k w ls v ρ hA
  obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := TS_some h
  · exact hA
  · exact ⟨hA.1, fun j hj => hA.2 j (by omega)⟩
  · exact hA

theorem TC_down : ∀ m i en, TC m i = some en →
    ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ := by
  intro m i en h k w ls v ρ hA
  have : en = enPark := by
    unfold TC at h; split at h
    · split at h
      · cases h; rfl
      · split at h
        · cases h; rfl
        · cases h
    · cases h
  subst this; exact hA

/-- **The resumer's guarantee at a park owning a lend's record** holds nothing at the lent cell. -/
theorem fdAt_lend {Fb : TFrame} {w' : TWd} {l : BoCa.Loc} :
    ∀ w ρf, fdAt enPark Val.unit Fb [lendRec (K := w'.K) l] w ρf → NoneAt (· = l) ρf :=
  fun _ _ h => (h.2 [lendRec l] (.cons (lendRec_rr l) .nil)).2.mono fun x hx => by
    subst hx; exact recMask_lendRec.mpr (Or.inl rfl)

open Classical in
/-- **End the lend and free the cell**: from the lend cell and its record, under a frame holding
nothing at the cell, `free ℓ` in any context, the record and the list's entries for it gone. -/
theorem twp_endFree {F : TFrame} {P : TPost} (hP : P.Down) (Kc : Kont) {l : BoCa.Loc} {α : Life}
    (hF : ∀ w ρf, F w ρf → NoneAt (· = l) ρf) {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    (h : twp (ℍ := ℍ) F P n w (ls.filter fun x => x.1 ≠ lendRec l) [] (Kc.plug (.val Val.unit))
      PMap.empty) :
    twp (ℍ := ℍ) F P n w ls [lendRec l] (Kc.plug (freeE (.val (.loc l)))) (viewRes α l) := by
  classical
  refine twp_lendEnd (Z := PMap.empty) (O₁ := []) (ls₁ := ls.filter fun x => x.1 ≠ lendRec l)
    (ResUT.CompS.comm (ResUT.compS_empty_right _)) (ResUT.CompS.comm (ResUT.compS_empty_right _))
    ⟨_, flat_empty⟩ (noneAt_empty _) hF (fun x => by simp) (by simp)
    (fun x hx => by
      by_cases h : x.1 = lendRec l
      · exact Or.inl h
      · exact Or.inr (List.mem_filter.mpr ⟨hx, by simpa using h⟩))
    (fun x hx => (List.mem_filter.mp hx).1)
    (fun x hx => by simpa using (List.mem_filter.mp hx).2) ?_
  exact twp_free hP Kc l Val.unit (ResUT.compS_empty_right _) h

open Classical in
/-- **`ubind`'s normal branch**: `ubind (λ_. free ℓ, D) ()` ends the lend and frees the cell. -/
theorem twp_resumeTail {F : TFrame} {P : TPost} (hP : P.Down) (Kc : Kont) {l : BoCa.Loc}
    {α : Life} (hF : ∀ w ρf, F w ρf → NoneAt (· = l) ρf) (D : Val) {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)}
    (h : twp (ℍ := ℍ) F P n w (ls.filter fun x => x.1 ≠ lendRec l) [] (Kc.plug (.val Val.unit))
      PMap.empty) :
    twp (ℍ := ℍ) F P n w ls [lendRec l] (Kc.plug ((ubK (Nf l) D).plug (.val Val.unit)))
      (viewRes α l) := by
  refine twp_det hP (fun μ => step1Only_plug (Head.uthen μ (Nf l) D Val.unit) rfl Kc) ?_
  refine twp_det hP (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl Kc) ?_
  exact twp_endFree hP Kc hF h

/-- A value answering `()` owning nothing. -/
theorem cerwpT_unit {T : OpTabT} {Fb F : TFrame} {n : Nat} {w : TWd} {ls : List (SRecT w.K)} :
    cerwpT (ℍ := ℍ) (opTableT T) QS Fb F n w ls [] (.val Val.unit) PMap.empty :=
  cerwpT_val (v := Val.unit) fun _ _ _ _ _ hr _ hO => by
    cases hO; exact ⟨rfl, rfl, RR.of_empty hr⟩

/-! ### The loan task -/

/-- `λa. ubind (λ_. free a, λ_. free a) (park ())`'s body. -/
def Lbody : Expr := .app (.app (.prim .ubind) (.pair (.lam (freeE (.var 1))) (.lam (freeE (.var 1)))))
  parkE
/-- **The loan task** `let a = alloc () in ubind (λ_. free a, λ_. free a) (park ())`. -/
def L : Expr := .app (.lam Lbody) (.app (.val (.prim .alloc)) (.val .unit))

theorem Lbody_beta (l : BoCa.Loc) :
    Lbody.subst 0 (Val.loc l) = (ubK (Nf l) (Nf l)).plug parkE := by
  simp [Lbody, ubK, Nf, parkE, Expr.subst, freeE, Kont.plug, performE, opPayload]
  repeat (first | rfl | constructor)

open Classical in
/-- **`ubind`'s finaliser at a cancel**: `ccatch (ubind (N, λ_. free ℓ) (raise cancel))` ends the
lend, frees the cell and answers `()`. -/
theorem twp_cancelTail {F : TFrame} {P : TPost} (hP : P.Down) {l : BoCa.Loc} {α : Life}
    (hF : ∀ w ρf, F w ρf → NoneAt (· = l) ρf) (N : Val) {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)}
    (h : twp (ℍ := ℍ) F P n w (ls.filter fun x => x.1 ≠ lendRec l) [] (.val Val.unit) PMap.empty) :
    twp (ℍ := ℍ) F P n w ls [lendRec l]
      (ccatchE ((ubK N (Nf l)).plug (raiseE (.val (cancelVal none))))) (viewRes α l) := by
  refine twp_det hP (fun μ => step1Only_plug (Head.ufinC μ N (Nf l) none .hole rfl) rfl ccK) ?_
  refine twp_det hP (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl cfK2) ?_
  refine twp_endFree hP cfK2 hF ?_
  refine twp_det hP (fun μ => step1Only_plug (Head.cfret μ none Val.unit) rfl ccK) ?_
  exact twp_det hP (fun μ => step1Only_plug (Head.cancel μ .hole rfl) rfl .hole) h

/-- The end of a run: `()`, owning nothing. -/
theorem twp_unitEnd {T : OpTabT} {Ψ : ContT} {Fb F : TFrame} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} :
    twp (ℍ := ℍ) F (cerwpPostT (opTableT T) QS Ψ Fb) n w ls [] (.val Val.unit) PMap.empty :=
  twp_here (fun μ => final_val μ Val.unit) fun _ _ _ _ _ hr _ hO => by
    cases hO; exact Or.inl ⟨Val.unit, rfl, rfl, rfl, RR.of_empty hr⟩

/-- **The stop at a park owning a lend**: from the lend's record and its cell, a continuation
whose resume and cancel branches, at the resumer's guarantee, each answer `()` owning nothing. -/
theorem cerwpT_parkLend {T : OpTabT} (hT0 : T nP 0 = some enPark)
    (hTd : ∀ m i en, T m i = some en → ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ)
    {Fb F : TFrame} {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {l : BoCa.Loc} {α : Life}
    (K : Kont) (hK : K.HasHnd nP = false)
    (hres : ∀ k', k' < n → ∀ (w' : TWd) (ls' : List (SRecT w'.K)),
      cerwpT (ℍ := ℍ) (opTableT T) QS Fb (fdAt enPark Val.unit Fb [lendRec (K := w'.K) l]) k' w'
        ls' [lendRec l] (K.plug (.val Val.unit)) (viewRes α l))
    (hcan : ∀ k', k' < n → ∀ (w' : TWd) (ls' : List (SRecT w'.K)),
      cerwpT (ℍ := ℍ) (opTableT T) QS Fb (fdAt enPark Val.unit Fb [lendRec (K := w'.K) l]) k' w'
        ls' [lendRec l] (ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))) (viewRes α l)) :
    cerwpT (ℍ := ℍ) (opTableT T) QS Fb F n w ls [lendRec l] (K.plug parkE) (viewRes α l) := by
  refine cerwpT_perform K hK hT0 rfl ?_
  intro w₀ ρ₀ ls₀ O₀ _ hr _ hO
  obtain rfl := rr_view_eq hr
  have hO₀ : ∀ {K K' : WCactus} {Θ : CodeTy} {O'' : List (FrameRecT K')},
      RecsRR Θ [lendRec (K := K) l] O'' → O'' = [lendRec l] := by
    intro K K' Θ O'' h
    cases h with
    | cons h₁ t => cases t; rw [RecRR.func h₁ (lendRec_rr l)]
  obtain rfl := hO₀ hO
  refine ⟨trivial, PMap.empty, viewRes α l, ResUT.CompS.comm (ResUT.compS_empty_right _),
    ⟨rfl, rfl⟩, (⟨(fun h => by cases h), fun w' ρ' ls' O' _ hr' _ hO' => ?_⟩ :
      contShareT enPark Fb n w₀ ls₀ [lendRec l] K Val.unit
        (cerwpTC (ℍ := ℍ) (opTableT T) QS Fb n) (viewRes α l))⟩
  obtain rfl := hO₀ hO'
  obtain rfl := rr_view_eq hr'
  refine ⟨fun k' hk' a σ σ' hB hcσ => ?_, fun _ _ k' hk' => ?_⟩
  · obtain ⟨rfl, rfl⟩ := hB
    obtain rfl := compS_empty_right_eq hcσ
    simp only [cerwpTC, hk', if_true]
    exact hres k' hk' w' ls'
  · simp only [cerwpTC, hk', if_true]
    exact hcan k' hk' w' ls'

/-- **The loan task at any table with `park`**, owning nothing, at every index and frame
condition: it allocates, opens a lend of the cell and parks holding the lend cell (a view, its
own copy) with the lend's record open; resumed or cancelled, it merges the view back, ends the
lend at the resumer's guarantee, frees the cell and answers `()` owning nothing. -/
theorem L_cerwpT {T : OpTabT} (hT0 : T nP 0 = some enPark)
    (hTd : ∀ m i en, T m i = some en → ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ)
    (α : Life) (n : Nat) (Fb F : TFrame) (w : TWd) (ls : List (SRecT w.K)) :
    cerwpT (ℍ := ℍ) (opTableT T) QS Fb F n w ls [] L PMap.empty := by
  have hD := post_down hTd (Ψ := cerwpTC (ℍ := ℍ) (opTableT T) QS Fb n) (F := Fb)
  rw [cerwpT_eq]
  refine twp_alloc_here hD (.appR (.lam Lbody) .hole) Val.unit fun l ρ₁ hc => ?_
  obtain rfl := compS_empty_left_eq hc
  refine twp_lendOpen α (Z := PMap.empty) (ResUT.CompS.comm (ResUT.compS_empty_right _))
    (ResUT.CompS.comm (ResUT.compS_empty_right _)) ?_
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ Lbody (Val.loc l)) rfl .hole) ?_
  rw [Kont.plug, Lbody_beta, ← cerwpT_eq]
  refine cerwpT_parkLend hT0 hTd (ubK (Nf l) (Nf l)) rfl (fun k' _ w' ls' => ?_)
    (fun k' _ w' ls' => ?_)
  · rw [cerwpT_eq]
    exact twp_resumeTail (post_down hTd) .hole fdAt_lend (Nf l) twp_unitEnd
  · rw [cerwpT_eq]
    exact twp_cancelTail (post_down hTd) fdAt_lend (Nf l) twp_unitEnd

/-! ### The loan task whose finaliser parks -/

def Dbody : Expr := .app (.app (.prim .ubind) (.pair (.lam (freeE (.var 2))) (.lam (freeE (.var 2)))))
  parkE
def LCbody : Expr := .app (.app (.prim .ubind) (.pair (.lam (freeE (.var 1))) (.lam Dbody))) parkE
/-- **The loan task with a parking finaliser**: `let a = alloc () in ubind (λ_. free a,
λ_. ubind (λ_. free a, λ_. free a) (park ())) (park ())`. -/
def LC : Expr := .app (.lam LCbody) (.app (.val (.prim .alloc)) (.val .unit))

/-- The finaliser: `λ_. ubind (λ_. free ℓ, λ_. free ℓ) (park ())`. -/
def Dc (l : BoCa.Loc) : Val := Val.lam ((ubK (Nf l) (Nf l)).plug parkE)

theorem LCbody_beta (l : BoCa.Loc) :
    LCbody.subst 0 (Val.loc l) = (ubK (Nf l) (Dc l)).plug parkE := by
  simp [LCbody, Dbody, ubK, Nf, Dc, parkE, Expr.subst, freeE, Kont.plug, performE, opPayload]
  repeat (first | rfl | constructor)

theorem Dc_beta (l : BoCa.Loc) :
    ((ubK (Nf l) (Nf l)).plug parkE).subst 0 Val.unit = (ubK (Nf l) (Nf l)).plug parkE := by
  simp [ubK, Nf, parkE, Expr.subst, freeE, Kont.plug, performE, opPayload]
  repeat (first | rfl | constructor)

/-- The finaliser's park in its frames: `ccatch (cfin c (ubind (N, N) [·]))`. -/
def K3 (l : BoCa.Loc) : Kont :=
  .appR (.prim .ccatch) (.appR (.app (.prim .cfin) (cancelVal none).1) (ubK (Nf l) (Nf l)))
def K4 : Kont := .appR (.prim .ccatch) (.appR (.app (.prim .cfin) (cancelVal none).1)
  (.appR (.app (.prim .cfin) (cancelVal none).1) .hole))

/-- **`LC`'s cancel branch**: the finaliser runs, parks holding the lend cell with its record
open, and resumed or cancelled again ends the lend, frees the cell and answers `()`. -/
theorem LC_cancel {T : OpTabT} (hT0 : T nP 0 = some enPark)
    (hTd : ∀ m i en, T m i = some en → ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ)
    {l : BoCa.Loc} {α : Life} {n : Nat} {Fb F : TFrame} {w : TWd} {ls : List (SRecT w.K)} :
    cerwpT (ℍ := ℍ) (opTableT T) QS Fb F n w ls [lendRec l]
      (ccatchE ((ubK (Nf l) (Dc l)).plug (raiseE (.val (cancelVal none))))) (viewRes α l) := by
  have hD := post_down hTd (Ψ := cerwpTC (ℍ := ℍ) (opTableT T) QS Fb n) (F := Fb)
  rw [cerwpT_eq]
  refine twp_det hD (fun μ => step1Only_plug (Head.ufinC μ (Nf l) (Dc l) none .hole rfl) rfl ccK) ?_
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl cfK2) ?_
  rw [Dc_beta, ← cerwpT_eq]
  refine cerwpT_parkLend hT0 hTd (K3 l) rfl (fun k' _ w' ls' => ?_) (fun k' _ w' ls' => ?_)
  · have hD' := post_down hTd (Ψ := cerwpTC (ℍ := ℍ) (opTableT T) QS Fb k') (F := Fb)
    rw [cerwpT_eq]
    refine twp_resumeTail hD' cfK2 fdAt_lend (Nf l) ?_
    refine twp_det hD' (fun μ => step1Only_plug (Head.cfret μ none Val.unit) rfl ccK) ?_
    exact twp_det hD' (fun μ => step1Only_plug (Head.cancel μ .hole rfl) rfl .hole) twp_unitEnd
  · have hD' := post_down hTd (Ψ := cerwpTC (ℍ := ℍ) (opTableT T) QS Fb k') (F := Fb)
    rw [cerwpT_eq]
    refine twp_det hD' (fun μ => step1Only_plug (Head.ufinC μ (Nf l) (Nf l) none .hole rfl) rfl
      cfK2) ?_
    refine twp_det hD' (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl K4) ?_
    refine twp_endFree hD' K4 fdAt_lend ?_
    refine twp_det hD' (fun μ => step1Only_plug (Head.cfret μ none Val.unit) rfl cfK2) ?_
    refine twp_det hD' (fun μ => step1Only_plug (Head.cfcancel μ none none .hole rfl) rfl ccK) ?_
    exact twp_det hD' (fun μ => step1Only_plug (Head.cancel μ .hole rfl) rfl .hole) twp_unitEnd

/-- **`LC` at any table with `park`**, owning nothing: as `L`, its cancel branch's finaliser
parking again (`LC_cancel`). -/
theorem LC_cerwpT {T : OpTabT} (hT0 : T nP 0 = some enPark)
    (hTd : ∀ m i en, T m i = some en → ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ)
    (α : Life) (n : Nat) (Fb F : TFrame) (w : TWd) (ls : List (SRecT w.K)) :
    cerwpT (ℍ := ℍ) (opTableT T) QS Fb F n w ls [] LC PMap.empty := by
  have hD := post_down hTd (Ψ := cerwpTC (ℍ := ℍ) (opTableT T) QS Fb n) (F := Fb)
  rw [cerwpT_eq]
  refine twp_alloc_here hD (.appR (.lam LCbody) .hole) Val.unit fun l ρ₁ hc => ?_
  obtain rfl := compS_empty_left_eq hc
  refine twp_lendOpen α (Z := PMap.empty) (ResUT.CompS.comm (ResUT.compS_empty_right _))
    (ResUT.CompS.comm (ResUT.compS_empty_right _)) ?_
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ LCbody (Val.loc l)) rfl .hole) ?_
  rw [Kont.plug, LCbody_beta, ← cerwpT_eq]
  refine cerwpT_parkLend hT0 hTd (ubK (Nf l) (Dc l)) rfl (fun k' _ w' ls' => ?_)
    (fun k' _ w' ls' => LC_cancel hT0 hTd)
  rw [cerwpT_eq]
  exact twp_resumeTail (post_down hTd) .hole fdAt_lend (Dc l) twp_unitEnd

end BoCa.Fig16.Tree.Wp.SchedProgs.SpawnProgs

end
