import Law2.Straight
import Law2.World
import Law2.Fragment
import GhostEnd.Open

/-!
# Law2 — Law 2, stated, with its open step enumerated

**Law 2**: a lend ended at a stop is re-lent at a fresh lifetime beneath the resumer's list, and
the suspended continuation is related at that lifetime — at any nesting of lends.

`law2` states it for a borrower Core's typing derives at a resuming row, holding a mixed stack of
lends open across its stops (`MixedStack`: `mut` lends of distinct places, `imm` lends, reborrows),
every operation of the row crossing every lend: beside the owners of the stack's lenders, the
borrower is its `ewpTS`, the owners handed back with its answer. Its proof is `fold_mixed` (every
lender's ghost end at a stop and re-lend at resume, by one induction on the stack) applied to the
borrower's piece, which is the one open step:

* **(S1) `piece_of_typed`**: a borrower Core's typing derives is D16.1's piece at its stack — at
  every stop of every run, the suspended continuation runs again at every re-lend of the stack,
  handed the views made afresh. **Not derived beyond the fragment; no obstruction verified.**

**What is proved of (S1).** `piece_of_bcomp` (`Law2/Fragment.lean`) is (S1) for every borrower whose
derivation lies in the fragment `BComp` of Core's typing, by one induction on the derivation
(`BComp.toPJ`): pure code with a frozen answer, `perform`, `let` holding any re-lendable frame
across the inner stops, `case`, `let (x, y) =`, `V; M`, closures that stop (built and called), and
`bounded_fix` at the row. `law2_frag` is Law 2 for it at every mixed stack; `Law2/FragInstances.lean`
discharges every hypothesis on a branch around a stop, a closure that stops, and a loop. (S1)
reduces to the piece judgment `PJ` holding of every derivation (`openS_of_pj`); what the fragment
leaves out is listed at `piece_of_typed`.

`law2_depth1` is the program-level statement at one lend: the resume rule's compatibility for the
borrow constant `withbor` at a resuming row. Its step at one lend:

* **(S1′) `relendOfTyped'`**: every borrower typed at a resuming row is GhostEnd's re-lendable
  callback (`RelendOfTyped'`: GhostEnd's `RelendOfTyped` with the bound `@bδ` defined, the hypothesis
  GhostEnd's own `relendOfTyped_of_rbodyOfTyped` adds). **Proved from (S1)** at the one-entry stack
  (`relend_of_openS₁`); at the fragment with no open step (`relend_frag`, `law2_depth1_frag`).

Outside `law2`'s class, not derived: an inner lend whose payload type reads the stack's own
variables (a borrow of a borrow opened inside the region; the stacked views read payloads at the
outer reading), a reborrow of an `imm` view (6.150 at a resuming table), a continuation typed over
an `imm` view (the view a re-lend hands carries no record for the `Imm` clause's coherence), a stop
handled between two lenders (`AllCross` at constant `true`), and the borrow constants' frames as
machine frames at a stack (GhostEnd #275).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Law2
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Head Step1N)
open BoCa.Lifetime (LifeVar LifeCtx LSub)
open GhostEnd

section
variable {δ : LSub}

/-- **(S1) Not derived beyond the fragment.** A borrower Core's typing derives at a resuming row —
linear operations answered at `1` whose arguments are closed data, free of every lend's variable
and outliving every lifetime (`Row.Resume`), so no lend escapes in a payload — its context rebuilt
from the views at every re-lend below `αi` and its answer in `[top]`, is D16.1's piece at the
stack, holding nothing of its own.

Proved for the derivations of the fragment `BComp` (`piece_of_bcomp`). It reduces to the piece
judgment at every derivation (`openS_of_pj`). The derivations outside the fragment, each not
derived, no obstruction verified:
* a pure computation whose answer is not frozen (a view, or a closure over one, returned by a pure
  call; `Mut`/`Imm` at a stack variable, an arrow or `∀` held across a stop): its answer has to be
  re-lendable (`RSlot`), which the kernel's fundamental property does not record; at first-order
  types this is GhostEnd's `lok_thaws` at a stack;
* a handler installed inside the borrower (`[handle]`): the stops of the operations it handles
  cross no lend (depth `0`), and `PJ` reads full-depth stops only (`AllCross`); GhostEnd #278;
* `[then]`, `∀I`/`∀E` at a row, `&` at a row, `[sub]` widening the row, a closure that stops
  handed to pure code (`CtxNoEffT`), and a context given as one `𝒢⟦Γ⟧` at each re-lend (`hctx`
  here) rather than slot by slot (`RCtx`). -/
theorem piece_of_typed {S : Row} {σ : LStack} (_hS : ∀ e ∈ σ, Row.Resume S e.x)
    (_hx : AllCross σ (Row.tab S δ))
    (_hLR : LinResume (Row.tab S δ)) {ds : List Bool} {Qa : List SRec → Val → WProp}
    {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {B : VTy}
    (_hd : CDerives Δ Γ M (.comp (CTy.effOf S B))) {γ : List Val} {αi : List Life}
    (_hctx : ∀ (αs : List Life) (ls : List SRec), List.Forall₂ (· < ·) αs αi →
      List.IsChain (· < ·) αs → ∀ ρv, vwS δ [] σ ds αs ls ρv →
        Δ.Models (extS δ σ αs) ∧ ∃ ρg ρd, ResU.CompS ρg ρd ρv ∧ NoOwn ρd ∧
          gDenC (ℍ := ℍ) ls (extS δ σ αs) Γ γ ρg)
    (_hQ : ∀ (αs : List Life) ls v ρ, List.IsChain (· < ·) αs → αs.length = σ.length →
      vCE (ℍ := ℍ) none true B ls (extS δ σ αs) v ρ → boxTop αs (Qa ls v) ρ)
    (ls : List SRec) :
    OpenS (ℍ := ℍ) δ σ (Row.tab S δ) (cbQ δ σ Qa) σ.length ds αi [] ls (substAll γ M)
      PMap.empty := by
  sorry

/-- **Law 2, at every mixed stack.** A borrower Core's typing derives at a resuming row, holding a
mixed stack of lends open across its stops, every operation crossing every lend, its context
rebuilt from the views at every re-lend: beside the owners of the stack's lenders, it is its
`ewpTS`, the owners handed back with its answer. `fold_mixed` (D3) folds the lenders; the piece is
(S1). -/
theorem law2 {S : Row} (hLR : LinResume (Row.tab S δ)) (hL : (Row.tab S δ).Local) {β : Life}
    {σ : LStack} (hσ : MixedStack σ) (hS : ∀ e ∈ σ, Row.Resume S e.x)
    (hx : AllCross σ (Row.tab S δ))
    (hP : ∀ e ∈ σ, ∀ ls w ρ, vCE (ℍ := ℍ) none true e.T ls δ w ρ → ρ.InStratum β)
    (hadm : ∀ e ∈ σ, ∀ v, e.k = .imm v → AdmWf e.T δ)
    {Qa : List SRec → Val → WProp} (hQa : ∀ ls₁ ls₂ u ρ, Ext ls₁ ls₂ ρ → Qa ls₁ u ρ → Qa ls₂ u ρ)
    {ds : List Bool} {bs : List Life} (hds : ds.length = σ.length) (hbs : bs.length = σ.length)
    (hβ : ∀ a ∈ bs, a ≤ β) {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {B : VTy}
    (hd : CDerives Δ Γ M (.comp (CTy.effOf S B))) {γ : List Val}
    (hctx : ∀ (αs : List Life) (ls : List SRec), αs.length = σ.length →
      List.IsChain (· < ·) αs → (∀ a ∈ αs, a < ⊤) → ∀ ρv, vwS δ [] σ ds αs ls ρv →
        Δ.Models (extS δ σ αs) ∧ ∃ ρg ρd, ResU.CompS ρg ρd ρv ∧ NoOwn ρd ∧
          gDenC (ℍ := ℍ) ls (extS δ σ αs) Γ γ ρg)
    (hQ : ∀ (αs : List Life) ls v ρ, List.IsChain (· < ·) αs →
      vCE (ℍ := ℍ) none true B ls (extS δ σ αs) v ρ → boxTop αs (Qa ls v) ρ)
    (ls : List SRec) :
    Entails (ownersM (ℍ := ℍ) δ σ ls)
      (ewpTS (ℍ := ℍ) ls (substAll γ M) (opTable (Row.tab S δ)) (withOwnersM δ σ Qa)) :=
  fun ρo ho => fold_mixed hLR hL hσ hx hP hadm Qa hQa ds bs hds hbs hβ ls _ ρo PMap.empty ρo ho
    (fun ls₁ _ => piece_of_typed hS hx hLR hd
      (fun αs ls' hlt hch => hctx αs ls' ((List.Forall₂.length_eq hlt).trans hbs) hch
        (lt_top_of_forall₂ hlt))
      (fun αs ls' v ρ hch _ h => hQ αs ls' v ρ hch h) ls₁) (ResU.comp_empty_right ρo)

end

/-! ### At one lend -/

/-- The one-entry stack of a lend of `ℓ` at `'x`, crossed by every operation. -/
abbrev oneS (l : BoCa.Loc) (x : LifeVar) (T : VTy) : LStack := [⟨l, x, T, .mut, fun _ => true⟩]

theorem allCross_oneS (l : BoCa.Loc) (x : LifeVar) (T : VTy) (Tab : OpTab) :
    AllCross (oneS l x T) Tab := fun _ _ _ _ e he => by
  simp only [List.mem_singleton] at he; subst he; rfl

/-- The view at one lend is the borrow's value at the extended reading. -/
theorem view_one {δ : LSub} {l : BoCa.Loc} {x : LifeVar} {T : VTy} (hT : ¬ VFree x T)
    {α : Life} {ls : List SRec} {ρv : WRes}
    (hv : vwS δ [] (oneS l x T) [true] [α] ls ρv) :
    vCE (ℍ := ℍ) none true (.mut (.var x) T) ls (δ.extend x α) (.loc l) ρv := by
  obtain ⟨a, b, hc, ha, hb⟩ := hv
  obtain rfl := hb.1
  rw [ResU.CompS.functional hc (ResU.comp_empty_right a)]
  exact mutView hT (by simpa [vis, vwE] using ha)

/-- The answer at one lend: `𝒱⟦['x] B⟧` at the lend's reading is `[α] 𝒱⟦B⟧`. -/
theorem hQ_one {δ : LSub} {x : LifeVar} {B : VTy} (hB : ¬ VFree x B) {l : BoCa.Loc} {T : VTy}
    (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes) (_ : List.IsChain (· < ·) αs)
    (hlen : αs.length = (oneS l x T).length)
    (h : vCE (ℍ := ℍ) none true (.box (.var x) B) ls (extS δ (oneS l x T) αs) v ρ) :
    boxTop αs ((fun ls v => vCE (ℍ := ℍ) none true B ls δ v) ls v) ρ := by
  match αs, hlen with
  | [α], _ =>
    obtain ⟨α', hα', hb⟩ := h
    have e : α' = α := by
      have := hα'.symm.trans (interp_ext_self δ x α)
      exact Option.some.inj this
    subst e
    refine ⟨?_, fun a ha => ?_⟩
    · have e := congrFun (congrFun (vC_extend_of_not_free (ℍ := ℍ) hB true ls δ α') v) ρ
      show vCE (ℍ := ℍ) none true B ls δ v ρ
      exact e.mp hb.1
    · have h' : some α' = some a := ha
      cases h'
      exact hb.2

/-- **Every borrower typed at a resuming row is re-lendable at one lend**: GhostEnd's
`RelendOfTyped`, at a bound `@bδ` that is defined. -/
def RelendOfTyped' : Prop :=
  ∀ (Δ : LifeCtx) (δ : LSub) (x : LifeVar) (b : Lifetime.Life) (T B : VTy) (S : Row)
    (M : Expr), Δ.Models δ → (∃ β, b.interp δ = some β) → Δ.find? x = none →
    b.mentions x = false → (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x T → ¬ VFree x B → Row.Resume S x →
    CDerives (Δ.extend x b) [⟨.mut (.var x) T, true⟩] M
      (.comp (CTy.effOf S (.box (.var x) B))) →
    ∀ (l : BoCa.Loc) (ls : List SRec),
      Relend (opTable (Row.tab S δ)) l T δ (finPost l T B δ) ls (substAll [Val.loc l] M)
        PMap.empty

/-- **(S1′) from (S1)**: (S1) at the one-entry stack is D16.1's piece, which at one `mut` entry
is GhostEnd's `Relend` (`relend_of_openS₁`). The context is the view (`mutView`); every lend below
`@bδ` models `Δ, x ⊏ b` (`models_extend`). -/
theorem relendOfTyped' : RelendOfTyped' (ℍ := ℍ) := by
  intro Δ δ x b T B S M hδ ⟨β, hβ⟩ _ hbx hΔx hT hB hS hD l ls
  have hO := piece_of_typed (δ := δ) (σ := oneS l x T)
    (fun e he => by simp only [List.mem_singleton] at he; subst he; exact hS)
    (allCross_oneS l x T _) (hS.linResume δ) (ds := [true])
    (Qa := fun ls v => vCE (ℍ := ℍ) none true B ls δ v) hD (γ := [Val.loc l]) (αi := [β])
    (fun αs ls' hlt _ ρv hv => by
      match αs, hlt with
      | [α], .cons hα .nil =>
        exact ⟨models_extend hδ hbx hΔx hβ hα, ρv, PMap.empty, ResU.comp_empty_right ρv,
          noOwn_empty, pure_sep_mk trivial ⟨ρv, PMap.empty, ResU.comp_empty_right ρv,
            view_one hT hv, ⟨rfl, trivial⟩⟩⟩)
    (fun αs ls' v ρ hch hlen h => hQ_one hB αs ls' v ρ hch hlen h) ls
  exact relend_of_openS₁ (hS.linResume δ) (allCross_oneS l x T _)
    (fun _ _ _ h => h) hO

/-- O15.1's resume half for every typed borrower, given `RelendOfTyped'`: GhostEnd's
`withbor_of_relendOfTyped` at a defined bound. -/
theorem withbor_of_relendOfTyped' (H : RelendOfTyped' (ℍ := ℍ)) {Δ : LifeCtx} {δ : LSub}
    (hδ : Δ.Models δ) {x : LifeVar} {b : Lifetime.Life} (hb : ∃ β, b.interp δ = some β)
    (hx : Δ.find? x = none) (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {T B : VTy} (hT : ¬ VFree x T) (hB : ¬ VFree x B)
    {βP : Life} (hP : ∀ ls w σ, vCE (ℍ := ℍ) none true T ls δ w σ → σ.InStratum βP)
    {S : Row} (hS : Row.Resume S x) {M : Expr} (hM : closedAt 1 M = true)
    (hD : CDerives (Δ.extend x b) [⟨.mut (.var x) T, true⟩] M
      (.comp (CTy.effOf S (.box (.var x) B))))
    (l : BoCa.Loc) (v : Val) (ls : List SRec) :
    Entails (ptoOwn l v ⋆ vCE (ℍ := ℍ) none true T ls δ v)
      (cC (ℍ := ℍ) (CTy.effOf S (.tensor (.ref T) B)) ls δ
        (.app (.app withbor (.val (.loc l))) (.val ⟨.lam (.lam M), .lam⟩))) := by
  intro ρ hρ
  refine (cC_effOf S _ ls δ _ ρ).mpr ?_
  exact withbor_relend (Row.tab S δ) (Row.tab_plainCancel S δ) hP _ v
    (relend_lam2 (opTable_mono _) hM (H Δ δ x b T B S M hδ hb hx hbx hΔx hT hB hS hD l ls)) ρ hρ

/-- **Law 2 at one lend, at the program level**: the resume rule's compatibility for the borrow
constant at a resuming row — `withbor ℓ (Λ. λm. M)` from the owner, at `F_S (Ref T ⊗ B)`, the
lend's bound defined. From (S1′), which is (S1) at the one-entry stack. -/
theorem law2_depth1 {Δ : LifeCtx} {δ : LSub} (hδ : Δ.Models δ) {x : LifeVar}
    {b : Lifetime.Life} (hb : ∃ β, b.interp δ = some β) (hx : Δ.find? x = none)
    (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false) {T B : VTy} (hT : ¬ VFree x T)
    (hB : ¬ VFree x B) {βP : Life} (hP : ∀ ls w σ, vCE (ℍ := ℍ) none true T ls δ w σ → σ.InStratum βP)
    {S : Row} (hS : Row.Resume S x) {M : Expr} (hM : closedAt 1 M = true)
    (hD : CDerives (Δ.extend x b) [⟨.mut (.var x) T, true⟩] M
      (.comp (CTy.effOf S (.box (.var x) B))))
    (l : BoCa.Loc) (v : Val) (ls : List SRec) :
    Entails (ptoOwn l v ⋆ vCE (ℍ := ℍ) none true T ls δ v)
      (cC (ℍ := ℍ) (CTy.effOf S (.tensor (.ref T) B)) ls δ
        (.app (.app withbor (.val (.loc l))) (.val ⟨.lam (.lam M), .lam⟩))) :=
  withbor_of_relendOfTyped' relendOfTyped' hδ hb hx hbx hΔx hT hB hP hS hM hD l v ls

/-! ### At one lend, at the fragment: no open step -/

/-- The view at one lend is re-lendable: frozen part `∅`, the view handed afresh at every re-lend. -/
theorem rctx_one {δ : LSub} {l : BoCa.Loc} {x : LifeVar} {T : VTy} (hT : ¬ VFree x T)
    {α : Life} {ls : List SRec} {ρv : WRes} (hv : vwS δ [] (oneS l x T) [true] [α] ls ρv) :
    RCtx (ℍ := ℍ) δ (oneS l x T) [α] ls [⟨.mut (.var x) T, true⟩] [Val.loc l] ρv := by
  refine pure_sep_mk trivial ⟨ρv, PMap.empty, ResU.comp_empty_right ρv, ?_, ⟨rfl, trivial⟩⟩
  show RelendableS δ [] (oneS l x T)
    (fun αs' ls' => vCE (ℍ := ℍ) none true (.mut (.var x) T) ls' (extS δ (oneS l x T) αs')
      (Val.loc l)) [α] ls ρv
  refine ⟨[true], PMap.empty, ρv, compS_empty_left ρv, hv, fun a _ => ResU.inStratum_empty a,
    fun ls' _ αs' hr ρv' τ hv' hc => ?_⟩
  rw [eq_of_compS_empty_left hc]
  match αs', hr.1 with
  | [α'], _ => exact view_one hT hv'

/-- **(S1′) at the fragment, with no open step.** A borrower of the fragment at a resuming row is
GhostEnd's re-lendable callback at every lend of its place. -/
theorem relend_frag {Δ : LifeCtx} {δ : LSub} (hδ : Δ.Models δ) {x : LifeVar}
    {b : Lifetime.Life} {β : Life} (hβ : b.interp δ = some β)
    (hbx : b.mentions x = false) (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {T B : VTy} (hT : ¬ VFree x T) (hB : ¬ VFree x B) {S : Row} (hS : Row.Resume S x)
    (hSne : S ≠ []) {M : Expr} (l : BoCa.Loc)
    (hD : BComp (ℍ := ℍ) δ (oneS l x T) S (Δ.extend x b) [⟨.mut (.var x) T, true⟩] M
      (.box (.var x) B))
    (ls : List SRec) :
    Relend (opTable (Row.tab S δ)) l T δ (finPost l T B δ) ls (substAll [Val.loc l] M)
      PMap.empty := by
  have hO := piece_of_bcomp hSne (allCross_oneS l x T _) (hS.linResume δ) hD trivial
    (Qa := fun ls v => vCE (ℍ := ℍ) none true B ls δ v)
    (fun αs ls' v ρ hch hlen h => hQ_one hB αs ls' v ρ hch hlen h) (ds := [true]) (αi := [β])
    (ls := ls) (γ := [Val.loc l])
    (fun αs hlt _ => by
      match αs, hlt with
      | [α], .cons hα .nil => exact models_extend hδ hbx hΔx hβ hα)
    (fun αs ρv hlt _ hv => by
      match αs, hlt with
      | [α], .cons _ .nil =>
        exact ⟨ρv, PMap.empty, ResU.comp_empty_right ρv, noOwn_empty, rctx_one hT hv⟩)
  exact relend_of_openS₁ (hS.linResume δ) (allCross_oneS l x T _) (fun _ _ _ h => h) hO

/-- **Law 2 at one lend, at the program level, at the fragment**: `withbor ℓ (Λ. λm. M)` for a
borrower `M` of the fragment, with no open step. -/
theorem law2_depth1_frag {Δ : LifeCtx} {δ : LSub} (hδ : Δ.Models δ) {x : LifeVar}
    {b : Lifetime.Life} {β : Life} (hβ : b.interp δ = some β)
    (hbx : b.mentions x = false) (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {T B : VTy} (hT : ¬ VFree x T) (hB : ¬ VFree x B)
    {βP : Life} (hP : ∀ ls w σ, vCE (ℍ := ℍ) none true T ls δ w σ → σ.InStratum βP)
    {S : Row} (hS : Row.Resume S x) (hSne : S ≠ []) {M : Expr} (hM : closedAt 1 M = true)
    (l : BoCa.Loc)
    (hD : BComp (ℍ := ℍ) δ (oneS l x T) S (Δ.extend x b) [⟨.mut (.var x) T, true⟩] M
      (.box (.var x) B))
    (v : Val) (ls : List SRec) :
    Entails (ptoOwn l v ⋆ vCE (ℍ := ℍ) none true T ls δ v)
      (cC (ℍ := ℍ) (CTy.effOf S (.tensor (.ref T) B)) ls δ
        (.app (.app withbor (.val (.loc l))) (.val ⟨.lam (.lam M), .lam⟩))) := by
  intro ρ hρ
  refine (cC_effOf S _ ls δ _ ρ).mpr ?_
  exact withbor_relend (Row.tab S δ) (Row.tab_plainCancel S δ) hP _ v
    (relend_lam2 (opTable_mono _) hM
      (relend_frag hδ hβ hbx hΔx hT hB hS hSne l hD ls)) ρ hρ

end Law2

end
