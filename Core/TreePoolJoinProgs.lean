import Core.TreePoolSpawnProgs

/-!
# A lend shared by children at any depth, ended after the join, through `PoolSchedAdequacyT`  `[spec §62]`

Closed programs run under the scheduler `HS` (`Core/TreePoolSpawn.lean`), each safe and leak-free
through the general headline `poolSchedAdequacyT`, every premise discharged.

**The tree of tasks** `node d` (`d` a depth):

* `node 0 = λ_. park (); cancel (); ()`: holding a copy of a lend (`viewRes β a`), it parks
  (its sibling runs) and then cancels the stack's top if that is a ready task (a sibling), and
  ends holding its copy;
* `node (d + 1) = λ_. let _ = par (node d, node d) in ()`: holding a copy, it hands a copy to each
  child (`viewRes_dup`), waits as a joiner for both, and ends holding its copy and every copy they
  handed back.

**The root** `rootJ d = let a = alloc () in let _ = par (node d, node d) in free a`: it opens a
lend of `a` (`twp_lendOpen`), hands a copy to each child, and is resumed when every task above it
has ended, with the copies handed back to it (`ViewsT`). It ends the lend at the copies composed
(`twp_lendEnd_imm`: the composed copy at `a` is `imm(S, (), ∅)`, and in every world `S` is the
lend's lifetime) and frees `a`.

`progJoin_safe d` holds at every depth `d`: `progJoin_depth1` (`d = 0`) and `progJoin_depth3`
(`d = 2`, three levels of tasks below the root, every one holding a copy of the root's lend) are
its instances. The safety statements quantify over every interleaving `HS` performs.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.SchedProgs.JoinProgs
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.Tree.Wp.SchedProgs.Park
open BoCa.Fig16.Tree.Wp.SchedProgs.Stack
open BoCa.Fig16.Tree.Wp.SchedProgs.Spawn
open BoCa.Fig16.Tree.Wp.SchedProgs.SpawnProgs
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE opPayload hndE hndVal capTag clauseAt ccatchE raiseE
  cancelVal freeE)

/-! ### Copies of lends are valid -/

section ViewsValid
variable {K : WCactus}

theorem flatR_empty : ResUT.FlatR (PMap.empty : TRes K) PMap.empty :=
  ⟨PMap.empty, PMap.empty, BoCa.Fig16.Tree.agW_empty,
    ExWT.empty_of_all_imm (fun _ _ e => by simp at e), ResUT.compR_empty_right _⟩

/-- **The aliasable walk of copies exists**, sitting where they sit. -/
theorem ViewsT.ag_exists : ∀ (L : List BoCa.Loc) {Z : TRes K},
    (∀ x, Z.get x ≠ none → x ∈ L) → ViewsT Z →
      ∃ a, AgWT Z a ∧ ∀ l, Z.get l = none → a.get l = none
  | [], Z, hL, _ => by
      have hZ : Z = PMap.empty := PMap.ext fun x => by
        by_contra h
        exact absurd (hL x (by simpa using h)) (by simp)
      subst hZ
      exact ⟨PMap.empty, BoCa.Fig16.Tree.agW_empty, fun _ _ => by simp⟩
  | x :: L, Z, hL, hV => by
      classical
      cases ex : Z.get x with
      | none =>
          refine ViewsT.ag_exists L (fun y hy => ?_) hV
          rcases List.mem_cons.mp (hL y hy) with rfl | h
          · exact absurd ex hy
          · exact h
      | some ψ =>
          obtain ⟨S, rfl⟩ := hV x _ ex
          have hc : ResUT.CompS (Z.del x) (viewResS S x) Z := ResUT.del_compS ex
          obtain ⟨a₁, h₁, hn₁⟩ := ViewsT.ag_exists L (Z := Z.del x) (fun y hy => by
            by_cases hyx : y = x
            · subst hyx; simp at hy
            · rw [ResUT.del_get_ne _ hyx] at hy
              rcases List.mem_cons.mp (hL y hy) with h | h
              · exact absurd h hyx
              · exact h) (hV.del x)
          have h₂ : AgWT (viewResS (K := K) S x) (viewResS S x) :=
            AgWT.single_imm flatR_empty (ResUT.compR_empty_right _)
          have ha₁x : a₁.get x = none := hn₁ x (by simp)
          obtain ⟨a, ha⟩ := (ResUT.compR_defined_iff a₁ (viewResS S x)).mpr
            (ResUT.Compat.of_disjoint fun y => by
              by_cases hyx : y = x
              · subst hyx; exact Or.inl ha₁x
              · exact Or.inr (by rw [viewResS, ResUT.single_get_ne _ hyx]))
          refine ⟨a, (AgWT.split hc).mpr ⟨a₁, _, h₁, h₂, ha⟩, fun l hl => ?_⟩
          have hlx : l ≠ x := fun e => by rw [e, ex] at hl; cases hl
          have hσ₁ : a₁.get l = none := hn₁ l (by rw [ResUT.del_get_ne _ hlx]; exact hl)
          rcases ResUT.Comp.get ha l with ⟨-, -, f⟩ | ⟨χ, f₁, -, -⟩ | ⟨χ, -, f₂, -⟩ |
              ⟨χ₁, χ₂, χ, f₁, -, -, -⟩
          · exact f
          · rw [hσ₁] at f₁; cases f₁
          · rw [viewResS, ResUT.single_get_ne _ hlx] at f₂; cases f₂
          · rw [hσ₁] at f₁; cases f₁

/-- **Copies are valid**: their flattening is their aliasable walk. -/
theorem ViewsT.valid {Z : TRes K} (hV : ViewsT Z) : ResUT.Valid Z := by
  obtain ⟨L, hL⟩ := Z.finite
  obtain ⟨a, ha, -⟩ := ViewsT.ag_exists L (fun y hy => hL y hy) hV
  exact ⟨a, PMap.empty, a, exST_all_imm fun _ _ e => hV.kind e, ha, ResUT.comp_empty_left a⟩

end ViewsValid

/-! ### Stops holding copies -/

/-- `par (th₁, th₂)`. -/
def parE (v : Val) : Expr := performE (.val (opPayload nP 3 v))

theorem post_downV {T : OpTabT}
    (hTd : ∀ m i en, T m i = some en → ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ)
    {Ψ : ContT} {F : TFrame} : (cerwpPostT (opTableT T) QV Ψ F).Down :=
  cerwpPostT_down QV_down hTd

/-- A value answering `()` holding copies. -/
theorem cerwpT_unitV {T : OpTabT} {Fb F : TFrame} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {ρ : TRes w.K} (hV : ViewsT ρ) :
    cerwpT (ℍ := ℍ) (opTableT T) QV Fb F n w ls [] (.val Val.unit) ρ :=
  cerwpT_val (v := Val.unit) fun _ _ _ _ _ hr _ hO => by
    cases hO; exact ⟨rfl, rfl, hV.rr hr⟩

/-- **`(λ_. b) (op ())` at a cancellable `enPark` operation, holding copies**, owning nothing:
resumed, `b` holding the copies; its cancel answers `()` holding them. -/
theorem cerwpT_parkThenV {T : OpTabT}
    (hTd : ∀ m i en, T m i = some en → ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ)
    {i : UInt32} (hTi : T nP i = some enPark) {b : Expr} {Fb F : TFrame} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {ρ : TRes w.K} (hV : ViewsT ρ)
    (hb : ∀ k', k' < n → ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (ρ' : TRes w'.K), ViewsT ρ' →
      cerwpT (ℍ := ℍ) (opTableT T) QV Fb (fdAt enPark Val.unit Fb ([] : List (FrameRecT w'.K))) k'
        w' ls' [] (b.subst 0 Val.unit) ρ') :
    cerwpT (ℍ := ℍ) (opTableT T) QV Fb F n w ls []
      (.app (.lam b) (performE (.val (opPayload nP i Val.unit)))) ρ := by
  show cerwpT (ℍ := ℍ) (opTableT T) QV Fb F n w ls []
    ((Kont.appR (.lam b) .hole).plug (performE (.val (opPayload nP i Val.unit)))) ρ
  refine cerwpT_perform (.appR (.lam b) .hole) rfl hTi rfl ?_
  intro w₀ ρ₀ ls₀ O₀ _ hr _ hO
  cases hO
  have hV₀ := hV.rr hr
  refine ⟨trivial, PMap.empty, ρ₀, ResUT.CompS.comm (ResUT.compS_empty_right _), ⟨rfl, rfl⟩,
    (⟨(fun h => by cases h), fun w' ρ' ls' O' _ hr' _ hO' => ⟨fun k' hk' a σ σ' hB hcσ => ?_,
      (fun _ _ k' hk' => ?_)⟩⟩ : contShareT enPark Fb n w₀ ls₀ [] (.appR (.lam b) .hole) Val.unit
        (cerwpTC (ℍ := ℍ) (opTableT T) QV Fb n) ρ₀)⟩
  · obtain ⟨rfl, rfl⟩ := hB
    obtain rfl : ρ' = σ' := (compS_empty_right_eq hcσ).symm
    cases hO'
    simp only [cerwpTC, hk', if_true]
    exact cerwpT_det (post_downV hTd) (fun μ => step1Only_plug (Head.beta μ b Val.unit) rfl .hole)
      (hb k' hk' w' ls' ρ' (hV₀.rr hr'))
  · cases hO'
    simp only [cerwpTC, hk', if_true]
    exact cerwpT_det (post_downV hTd) (fun μ => step1Only_plug (Head.cancel μ _ rfl) rfl .hole)
      (cerwpT_unitV (hV₀.rr hr'))

/-- The records a run owns at a `par` stop, one list at every carrier, carried by re-reading. -/
def RecsFixed (Os : (K : WCactus) → List (FrameRecT K)) : Prop :=
  ∀ (K K' : WCactus) (Θ : CodeTy) (O'' : List (FrameRecT K')), RecsRR Θ (Os K) O'' → O'' = Os K'

theorem recsFixed_nil : RecsFixed fun _ => [] := by
  intro K K' Θ O'' h; cases h; rfl

theorem recsFixed_lend (l : BoCa.Loc) : RecsFixed fun _ => [lendRec l] := by
  intro K K' Θ O'' h
  cases h with
  | cons h₁ t => cases t; rw [RecRR.func h₁ (lendRec_rr l)]

theorem relFT_view (β : Life) (l : BoCa.Loc) {K : WCactus} :
    RelFT (lendRec (K := K) l) (viewRes β l) :=
  ⟨l, FrzT.imm (ResUT.single_get_self _ _) rfl, Or.inl rfl⟩

/-- **`(λ_. b) (par (th₁, th₂))` at a table `tabOf Tc`, holding a copy `viewRes β ℓ`**: each child
gets a copy (`viewRes_dup`) and is verified at the children's tables holding it; the parent,
owning the records `Os`, keeps its copy and is resumed with the copies handed back to it
(`ViewsT`), at every list keeping the records of its stop list its copy reads. -/
theorem cerwpT_parThen {Tc : Nat → OpTabT} {th₁ th₂ : Val} {n : Nat} {β : Life} {l : BoCa.Loc}
    (hth₁ : ∀ j, j < n → ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (Fb' Fe' : TFrame),
      (∀ w ρf, ResUT.Valid ρf → Fb' w ρf) → (∀ w ρf, fdMask (fun _ => False) w ρf → Fe' w ρf) →
      cerwpT (ℍ := ℍ) (opTableT (Tc j)) QV Fb' Fe' j w' ls' [] (.app th₁.1 (.val Val.unit))
        (viewRes β l))
    (hth₂ : ∀ j, j < n → ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (Fb' Fe' : TFrame),
      (∀ w ρf, ResUT.Valid ρf → Fb' w ρf) → (∀ w ρf, fdMask (fun _ => False) w ρf → Fe' w ρf) →
      cerwpT (ℍ := ℍ) (opTableT (Tc j)) QV Fb' Fe' j w' ls' [] (.app th₂.1 (.val Val.unit))
        (viewRes β l))
    {Os : (K : WCactus) → List (FrameRecT K)} (hOs : RecsFixed Os)
    {b : Expr} {Fb F : TFrame} {w : TWd} {ls : List (SRecT w.K)}
    (hb : ∀ k', k' < n → ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (σ σ' : TRes w'.K),
      (lendRec l ∈ rsOfT ls → lendRec l ∈ rsOfT ls') → ViewsT σ →
      ResUT.CompS (viewRes β l) σ σ' →
      cerwpT (ℍ := ℍ) (opTableT (tabOf (ℍ := ℍ) Tc)) QV Fb
        (fdAt (enParP (parPA (ℍ := ℍ) Tc)) (Val.pair th₁ th₂) Fb (Os w'.K)) k' w' ls' (Os w'.K)
        (b.subst 0 Val.unit) σ') :
    cerwpT (ℍ := ℍ) (opTableT (tabOf (ℍ := ℍ) Tc)) QV Fb F n w ls (Os w.K)
      (.app (.lam b) (parE (Val.pair th₁ th₂))) (viewRes β l) := by
  show cerwpT (ℍ := ℍ) (opTableT (tabOf (ℍ := ℍ) Tc)) QV Fb F n w ls (Os w.K)
    ((Kont.appR (.lam b) .hole).plug (performE (.val (opPayload nP 3 (Val.pair th₁ th₂)))))
      (viewRes β l)
  refine cerwpT_perform (.appR (.lam b) .hole) rfl (tabOf_par Tc) rfl ?_
  intro w₀ ρ₀ ls₀ O₀ _ hr hl hO
  obtain rfl := rr_view_eq hr
  obtain rfl := hOs _ _ _ _ hO
  have hchild : ∀ {th : Val}, (∀ j, j < n → ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (Fb' Fe' : TFrame),
      (∀ w ρf, ResUT.Valid ρf → Fb' w ρf) → (∀ w ρf, fdMask (fun _ => False) w ρf → Fe' w ρf) →
      cerwpT (ℍ := ℍ) (opTableT (Tc j)) QV Fb' Fe' j w' ls' [] (.app th.1 (.val Val.unit))
        (viewRes β l)) → ChildOK (ℍ := ℍ) Tc n w₀ th (viewRes β l) := by
    intro th hth j hj w' ρ' ls' _ hr' Fb' Fe' h₁ h₂
    obtain rfl := rr_view_eq hr'
    exact hth j hj w' ls' Fb' Fe' h₁ h₂
  -- the lend's record, if the stop list carries it, is carried by the list at the stop's world
  have hl₀ : lendRec l ∈ rsOfT ls → lendRec l ∈ rsOfT ls₀ := fun h => by
    obtain ⟨⟨r, α⟩, hr₁, rfl⟩ := List.mem_map.mp h
    obtain ⟨y, hy, hry, -⟩ := forall₂_mem_left hl hr₁
    exact List.mem_map.mpr ⟨y, hy, RecRR.func hry (lendRec_rr l)⟩
  refine ⟨trivial, viewRes β l, viewRes β l, viewRes_dup β l,
    ⟨th₁, th₂, viewRes β l, viewRes β l, rfl, viewRes_dup β l, ViewsT.view β l, ViewsT.view β l,
      hchild hth₁, hchild hth₂⟩,
    (⟨(fun h => by cases h), fun w' ρ' ls' O' _ hr' hx hO' => ⟨fun k' hk' a σ σ' hB hcσ => ?_,
      (fun hq => absurd rfl hq)⟩⟩ : contShareT (enParP (parPA (ℍ := ℍ) Tc)) Fb n w₀ ls₀ (Os w₀.K)
        (.appR (.lam b) .hole) (Val.pair th₁ th₂)
        (cerwpTC (ℍ := ℍ) (opTableT (tabOf (ℍ := ℍ) Tc)) QV Fb n) (viewRes β l))⟩
  obtain ⟨rfl, hV⟩ := hB
  obtain rfl := rr_view_eq hr'
  obtain rfl := hOs _ _ _ _ hO'
  have hls : lendRec l ∈ rsOfT ls → lendRec l ∈ rsOfT ls' := fun h => by
    obtain ⟨r', hr'm, hrr⟩ := hx (lendRec l) (hl₀ h) (relFT_view β l)
    rwa [RecRR.func hrr (lendRec_rr l)] at hr'm
  simp only [cerwpTC, hk', if_true]
  exact cerwpT_det (post_downV (tabOf_down Tc)) (fun μ => step1Only_plug (Head.beta μ b Val.unit)
    rfl .hole) (hb k' hk' w' ls' σ σ' hls hV hcσ)

/-! ### The tree of tasks -/

/-- `λ_. park (); cancel (); ()`, as `thC`. -/
def node : Nat → Val
  | 0 => thC
  | d + 1 => Val.lam (.app (.lam (.val .unit)) (parE (Val.pair (node d) (node d))))

theorem node_closed : ∀ d, closedAt 0 (node d).1 = true
  | 0 => by
      simp [node, thC, Cbody, parkE, cancelE, performE, opPayload, closedAt, Val.lam]
      repeat (first | rfl | constructor)
  | d + 1 => by
      simp [node, parE, performE, opPayload, closedAt, Val.lam, Val.pair]
      exact ⟨rfl, closedAt_mono _ (node_closed d) (Nat.zero_le _)⟩

theorem node_subst (d j : Nat) (s : Val) : Expr.subst j s (node d).1 = (node d).1 :=
  subst_closedAt _ s (node_closed d) (Nat.zero_le j)

theorem tabAt_par (j : Nat) :
    tabAt (ℍ := ℍ) j nP 3 = some (enParP (parPA (ℍ := ℍ)
      (fun i => if i < j then tabAt (ℍ := ℍ) i else OpTabT.empty))) := by
  rw [tabAt_eq]; exact tabOf_par _

/-- **Every node of the tree, holding a copy, at every indexed table at its index**: a leaf parks
and cancels holding its copy; an inner node hands a copy to each child, joins them, and ends with
every copy. -/
theorem node_ok : ∀ (d j : Nat) (β : Life) (l : BoCa.Loc) (Fb Fe : TFrame) (w : TWd)
    (ls : List (SRecT w.K)),
    cerwpT (ℍ := ℍ) (opTableT (tabAt (ℍ := ℍ) j)) QV Fb Fe j w ls [] (.app (node d).1 (.val Val.unit))
      (viewRes β l)
  | 0, j, β, l, Fb, Fe, w, ls => by
      refine cerwpT_det (post_downV (tabAt_down j)) (fun μ => step1Only_plug
        (Head.beta μ Cbody Val.unit) rfl .hole) ?_
      have e : Cbody.subst 0 Val.unit = Cbody := by
        simp [Cbody, parkE, cancelE, Expr.subst, performE, opPayload]
        repeat (first | rfl | constructor)
      rw [Kont.plug, e]
      refine cerwpT_parkThenV (tabAt_down j) (tabAt_park j) (ViewsT.view β l)
        fun k' _ w'' ls'' ρ'' hV'' => ?_
      have e' : (Expr.app (.lam (.val Val.unit)) cancelE).subst 0 Val.unit =
          .app (.lam (.val Val.unit)) (performE (.val (opPayload nP 2 Val.unit))) := by
        simp [cancelE, Expr.subst, performE, opPayload]
        repeat (first | rfl | constructor)
      rw [e']
      exact cerwpT_parkThenV (tabAt_down j) (tabAt_cancel j) hV''
        fun k'' _ w₃ ls₃ ρ₃ hV₃ => cerwpT_unitV hV₃
  | d + 1, j, β, l, Fb, Fe, w, ls => by
      refine cerwpT_det (post_downV (tabAt_down j)) (fun μ => step1Only_plug
        (Head.beta μ _ Val.unit) rfl .hole) ?_
      have e : (Expr.app (.lam (.val .unit)) (parE (Val.pair (node d) (node d)))).subst 0 Val.unit =
          .app (.lam (.val .unit)) (parE (Val.pair (node d) (node d))) := by
        simp [parE, Expr.subst, performE, opPayload, Val.pair, node_subst]
        repeat (first | rfl | constructor)
      rw [Kont.plug, e, tabAt_eq]
      have hch : ∀ j', j' < j → ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (Fb' Fe' : TFrame),
          (∀ w ρf, ResUT.Valid ρf → Fb' w ρf) → (∀ w ρf, fdMask (fun _ => False) w ρf → Fe' w ρf) →
          cerwpT (ℍ := ℍ) (opTableT ((fun i => if i < j then tabAt (ℍ := ℍ) i else OpTabT.empty) j'))
            QV Fb' Fe' j' w' ls' [] (.app (node d).1 (.val Val.unit)) (viewRes β l) := by
        intro j' hj' w' ls' Fb' Fe' _ _
        simp only [hj', if_true]
        exact node_ok d j' β l Fb' Fe' w' ls'
      exact cerwpT_parThen (Os := fun _ => []) hch hch recsFixed_nil
        fun k' _ w' ls' σ σ' _ hV hcσ => by
          have e₀ : Expr.subst 0 Val.unit (.val Val.unit) = .val Val.unit := rfl
          rw [e₀]
          exact cerwpT_unitV ((ViewsT.view β l).compS hcσ hV)

/-! ### The root -/

/-- The root's body under `a`: `let _ = par (node d, node d) in free a`. -/
def rootB (d : Nat) : Expr := .app (.lam (freeE (.var 1))) (parE (Val.pair (node d) (node d)))

/-- **The root** `let a = alloc () in let _ = par (node d, node d) in free a`. -/
def rootJ (d : Nat) : Expr := .app (.lam (rootB d)) (.app (.val (.prim .alloc)) (.val .unit))

theorem rootB_beta (d : Nat) (l : BoCa.Loc) :
    (rootB d).subst 0 (Val.loc l) =
      .app (.lam (freeE (.val (Val.loc l)))) (parE (Val.pair (node d) (node d))) := by
  simp [rootB, parE, freeE, Expr.subst, performE, opPayload, Val.pair, node_subst]
  repeat (first | rfl | constructor)

theorem fdAt_par_lend {P : TVProp} {v : Val} {Fb : TFrame} {w' : TWd} {l : BoCa.Loc} :
    ∀ w ρf, fdAt (enParP P) v Fb [lendRec (K := w'.K) l] w ρf → NoneAt (· = l) ρf :=
  fun _ _ h => (h.2 [lendRec l] (.cons (lendRec_rr l) .nil)).2.mono fun x hx => by
    subst hx; exact recMask_lendRec.mpr (Or.inl rfl)

open Classical in
/-- **End the lend at the copies handed back, and free the cell**: the root's copy `viewRes α ℓ`
beside the copies `σ` handed back to it, under a frame holding nothing at `ℓ`, the list carrying
the lend's record. The copies at `ℓ` compose with the root's into `imm(S, (), ∅)`
(`ViewsT.split_at`, `viewResS_compS`) and the lend ends there (`twp_lendEnd_imm`); the copies
elsewhere stay, and `free ℓ` frees the cell. -/
theorem twp_joinEndFree {F : TFrame} {P : TPost} (hP : P.Down) (Kc : Kont) {l : BoCa.Loc}
    {α : Life} (hF : ∀ w ρf, F w ρf → NoneAt (· = l) ρf) {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} (hls : lendRec l ∈ rsOfT ls) {σ σ' : TRes w.K} (hV : ViewsT σ)
    (hcσ : ResUT.CompS (viewRes α l) σ σ')
    (h : ∀ Z : TRes w.K, ViewsT Z →
      twp (ℍ := ℍ) F P n w (ls.filter fun x => x.1 ≠ lendRec l) [] (Kc.plug (.val Val.unit)) Z) :
    twp (ℍ := ℍ) F P n w ls [lendRec l] (Kc.plug (freeE (.val (.loc l)))) σ' := by
  classical
  -- `σ′ = Z ● imm(S, (), ∅)` at `ℓ`, `Z` the copies elsewhere
  obtain ⟨Z, S, hZ, hZl, hρ⟩ : ∃ (Z : TRes w.K) (S : TSet), ViewsT Z ∧ Z.get l = none ∧
      ResUT.CompS Z (viewResS S l) σ' := by
    rcases hV.split_at l with hσl | ⟨T, hT⟩
    · exact ⟨σ, TSet.single α, hV, hσl, ResUT.CompS.comm hcσ⟩
    · obtain ⟨y, hy₁, hy₂⟩ := (ResUT.CompS.assoc (viewRes α l) (σ.del l) (viewResS T l) σ').mp
        ⟨σ, hT, hcσ⟩
      obtain ⟨x, hx₁, hx₂⟩ := (ResUT.CompS.assoc (σ.del l) (viewRes α l) (viewResS T l) σ').mpr
        ⟨y, ResUT.CompS.comm hy₁, hy₂⟩
      obtain rfl := ResUT.CompS.functional hx₁ (viewResS_compS (TSet.single α) T l)
      exact ⟨σ.del l, TSet.single α ∪ T, ViewsT.del hV l, ResUT.del_get_self _ _, hx₂⟩
  obtain ⟨ρ₁, hρ₁⟩ := (ResUT.compS_defined_iff Z (ResUT.single l (CellUT.ownOf BoCa.Val.unit))).mpr
    (compatS_single_of_get_noneT hZl)
  refine twp_lendEnd_imm (O₁ := []) (ls₁ := ls.filter fun x => x.1 ≠ lendRec l) hρ hls hρ₁
    (ViewsT.valid hZ) (ViewsT.noneAt hZ hZl) hF (fun x => by simp) (by simp)
    (fun x hx => by
      by_cases h : x.1 = lendRec l
      · exact Or.inl h
      · exact Or.inr (List.mem_filter.mpr ⟨hx, by simpa using h⟩))
    (fun x hx => (List.mem_filter.mp hx).1)
    (fun x hx => by simpa using (List.mem_filter.mp hx).2) ?_
  exact twp_free hP Kc l Val.unit (ResUT.CompS.comm hρ₁) (h Z hZ)

/-- **The root at every indexed table**, owning nothing: it allocates, opens a lend, hands a copy
to each child (`cerwpT_parThen`), and resumed with the copies handed back ends the lend at them and
frees the cell (`twp_joinEndFree`), answering `()` holding the copies at other locations. -/
theorem rootJ_cerwpT (d : Nat) (α : Life) {k n : Nat} (hn : n ≤ k) (Fb F : TFrame) (w : TWd)
    (ls : List (SRecT w.K)) :
    cerwpT (ℍ := ℍ) (opTableT (tabAt (ℍ := ℍ) k)) QV Fb F n w ls [] (rootJ d) PMap.empty := by
  have hD := post_downV (tabAt_down k) (Ψ := cerwpTC (ℍ := ℍ) (opTableT (tabAt (ℍ := ℍ) k)) QV Fb n)
    (F := Fb)
  rw [cerwpT_eq]
  refine twp_alloc_here hD (.appR (.lam (rootB d)) .hole) Val.unit fun l ρ₁ hc => ?_
  obtain rfl := compS_empty_left_eq hc
  refine twp_lendOpen α (Z := PMap.empty) (ResUT.CompS.comm (ResUT.compS_empty_right _))
    (ResUT.CompS.comm (ResUT.compS_empty_right _)) ?_
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ (rootB d) (Val.loc l)) rfl .hole) ?_
  rw [Kont.plug, rootB_beta, ← cerwpT_eq, tabAt_eq]
  have hch : ∀ j', j' < n → ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (Fb' Fe' : TFrame),
      (∀ w ρf, ResUT.Valid ρf → Fb' w ρf) → (∀ w ρf, fdMask (fun _ => False) w ρf → Fe' w ρf) →
      cerwpT (ℍ := ℍ) (opTableT ((fun i => if i < k then tabAt (ℍ := ℍ) i else OpTabT.empty) j'))
        QV Fb' Fe' j' w' ls' [] (.app (node d).1 (.val Val.unit)) (viewRes α l) := by
    intro j' hj' w' ls' Fb' Fe' _ _
    simp only [show j' < k by omega, if_true]
    exact node_ok d j' α l Fb' Fe' w' ls'
  refine cerwpT_parThen (Os := fun _ => [lendRec l]) hch hch (recsFixed_lend l)
    fun k' _ w' ls' σ σ' hls hV hcσ => ?_
  have hD' := post_downV (tabOf_down (fun i => if i < k then tabAt (ℍ := ℍ) i else OpTabT.empty))
    (Ψ := cerwpTC (ℍ := ℍ) (opTableT (tabOf (ℍ := ℍ)
      (fun i => if i < k then tabAt (ℍ := ℍ) i else OpTabT.empty))) QV Fb k') (F := Fb)
  have e : (freeE (.val (Val.loc l))).subst 0 Val.unit = freeE (.val (Val.loc l)) := by
    simp [freeE, Expr.subst]
  rw [e, cerwpT_eq]
  exact twp_joinEndFree hD' .hole fdAt_par_lend
    (hls (List.mem_map.mpr ⟨(lendRec l, α), List.mem_cons_self, rfl⟩)) hV hcσ fun Z hZ =>
      twp_here (fun μ => final_val μ Val.unit) fun _ _ _ _ _ hr _ hO => by
        cases hO; exact Or.inl ⟨Val.unit, rfl, rfl, rfl, hZ.rr hr⟩

/-! ### The programs -/

/-- `(hnd HS (rootJ d)) (HS, [])`. -/
def progJoin (d : Nat) : Expr := progOf (rootJ d)

/-- **A lend shared by a tree of tasks, ended after the join, is safe and leak-free, or
diverges**, at every depth `d`, through `PoolSchedAdequacyT`, every premise discharged. The root
lends `a` to two children; every inner node hands its copy on to two children of its own and joins
them; every leaf parks (its siblings run) and cancels the stack's top when that is a ready sibling;
each task's end hands its copies to its parent. The root, resumed with every copy, ends the lend
at them and frees `a`. Every configuration reached steps or is a value; a value is reached only at
the empty memory; every `free` finds its cell. -/
theorem progJoin_safe (d : Nat) : OrDiverges (ℍ := ℍ) (progJoin d) :=
  poolSchedAdequacyT beforeP TJ nP qsS stackRet hsS QV QS InvS _ _ (rootJ d)
    (fun _ _ _ _ _ _ h => h.2.2) (fun _ h => by cases h) hs_schedOK (fun _ _ _ => trivial)
    (fun _ _ _ => trivial) fun n =>
      cerwpT_tabAt (rootJ_cerwpT d α₀ (k := n) le_rfl _ _ _ _)

/-- **Depth 1**: the root's lend shared by two leaves, interleaved, one possibly cancelled by the
other. -/
theorem progJoin_depth1 : OrDiverges (ℍ := ℍ) (progJoin 0) := progJoin_safe 0

/-- **Depth 3**: the root's lend shared through two levels of joiners down to eight leaves, every
task holding a copy, interleaved, leaves possibly cancelling their siblings. -/
theorem progJoin_depth3 : OrDiverges (ℍ := ℍ) (progJoin 2) := progJoin_safe 2

end BoCa.Fig16.Tree.Wp.SchedProgs.JoinProgs

end
