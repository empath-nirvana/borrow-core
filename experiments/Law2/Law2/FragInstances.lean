import Law2.Fragment
import Law2.Instances

/-!
# Law2 — borrowers of the fragment, every hypothesis discharged

Corollaries of `law2_frag`. The program derivations (`d_branch`, `d_closure`, `d_loop`) are stated
at every stack, reading, effect context and lifetime of the view; each instance discharges the
stack's hypotheses once (`law2_A`, `law2_C`). The setting is `Instances.lean`'s: a struct `s`
holding a borrow `Mut 'b 1` of an outer place, lent at `'x₁`, the generator holding the
innermost reborrow's view `m`, at the row `{yield : I32 ↠ 1}`.

At the depth-2 stack `[s@'x₂ reborrow, s@'x₁]`:

* `branch_spans`: **a value computed before a stop, held across it, and a branch around a second
  stop.** `c = inj₂ (); yield 1; case c of inj₁ _ ⇒ use m | inj₂ _ ⇒ yield 2; use m`. The frame of
  the first stop holds `c` and `m`; the second stop is inside a branch.
* `closure_stops_spans`: **a closure that stops**, built before a stop and called after it:
  `f = λ_. yield 2; yield 1; f (); use m`. The call stops inside the callee with both lends open.
* `loop_spans`: **a loop around a stop**: `bounded_fix (step, (3, ())); use m`, the step yielding
  once per iteration and calling the next through its self-reference; the view is held in the frame
  across every iteration's stop.

At the depth-3 reborrow chain `[s@'x₃ reborrow, s@'x₂ reborrow, s@'x₁]`: `chain3_loop_spans`,
`chain3_branch_spans`, the same programs at the innermost view.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Law2.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Head Step1N performE opPayload)
open BoCa.Lifetime (LifeVar LifeCtx LSub)
open GhostEnd GhostEnd.Instance
open Law2

/-! ### The reborrow's view, re-lendable -/

/-- The reborrow's type. -/
abbrev TM : VTy := .mut (.var 2) TA

/-- **The reborrow's view is a re-lendable value**: no part of it frozen, the view itself handed
afresh at every re-lend (`ctx_A`). -/
theorem rctx_view {s : BoCa.Loc} {αs : List Life} {ls : List SRec} {ρv : WRes}
    (hv : vwS δA [] [e₂ s, e₁ s] [true, true] αs ls ρv) :
    RCtx (ℍ := ℍ) δA [e₂ s, e₁ s] αs ls [⟨TM, true⟩] [Val.loc s] ρv := by
  refine pure_sep_mk trivial ⟨ρv, PMap.empty, ResU.comp_empty_right ρv, ?_, ⟨rfl, trivial⟩⟩
  show RelendableS δA [] [e₂ s, e₁ s]
    (fun αs' ls' => vCE (ℍ := ℍ) none true TM ls' (extS δA [e₂ s, e₁ s] αs') (Val.loc s)) αs ls ρv
  refine ⟨[true, true], PMap.empty, ρv, compS_empty_left ρv, hv, fun a _ => ResU.inStratum_empty a,
    fun ls' _ αs' hr ρv' τ hv' hc => ?_⟩
  rw [eq_of_compS_empty_left hc]
  match αs', hr.1 with
  | [α₂, α₁], _ =>
    have hA := ctx_A (ℍ := ℍ) (α₁ := α₁) (vwS_A hv')
    obtain ⟨-, hg⟩ := pure_sep_iff.mp hA
    unfold gSepC at hg
    rw [if_pos rfl] at hg
    obtain ⟨ρn, ρe, hcn, hn, he⟩ := hg
    obtain rfl : ρe = PMap.empty := he.1
    rw [ResU.CompS.functional hcn (ResU.comp_empty_right ρn)] at *
    exact hn

theorem hctx_view {s : BoCa.Loc} {bs : List Life} :
    ∀ αs ls ρv, List.Forall₂ (· < ·) αs bs → List.IsChain (· < ·) αs →
      vwS δA [] [e₂ s, e₁ s] [true, true] αs ls ρv →
        ∃ ρg ρd, ResU.CompS ρg ρd ρv ∧ NoOwn ρd ∧
          RCtx (ℍ := ℍ) δA [e₂ s, e₁ s] αs ls [⟨TM, true⟩] [Val.loc s] ρg :=
  fun _ _ ρv _ _ hv => ⟨ρv, PMap.empty, ResU.comp_empty_right ρv, noOwn_empty, rctx_view hv⟩

/-- `ΔA` models every re-lend of the stack below `[4, 3]`. -/
theorem hΔ_A {αs : List Life}
    (hle : List.Forall₂ (· ≤ ·) αs [OrderDual.toDual 4, OrderDual.toDual 3])
    (hch : List.IsChain (· < ·) αs) (s : BoCa.Loc) :
    ΔA.Models (extS δA [e₂ s, e₁ s] αs) := by
  match αs, hle with
  | [α₂, α₁], .cons _ (.cons h₁ .nil) =>
    exact models_A δA rfl (List.isChain_pair.mp hch)
      (lt_of_le_of_lt h₁ (by decide))

/-! ### The program -/

/-- `yield n`. -/
abbrev yE (n : UInt32) : Expr := performE (opArgE yieldOp.n yieldOp.i (.val (Val.i32 n)))

/-- `return forget to fg. fg m to z. return ()`, `m` at index `k`. -/
abbrev tailE (k : Nat) : Expr := bindE forget (bindE (.app (.var 0) (.var (k + 1))) (.val .unit))

/-- The second branch: `yield 2; use m`, `m` at index `3` in the branch. -/
abbrev brE : Expr := bindE (yE 2) (tailE 4)

/-- **The program.** `c = inj₂ (); yield 1; case c of inj₁ _ ⇒ use m | inj₂ _ ⇒ yield 2; use m`,
`m` at index `0`. -/
abbrev branchE : Expr :=
  bindE (.inj₂ (.val .unit)) (bindE (yE 1) (.case (.var 1) (tailE 3) brE))

/-- The type of `forget` at the reborrow. -/
abbrev fgTy : VTy := axForgetMutTy (.var 2) TA

theorem pu : VTy.Persistent .unit := rfl

/-- `use m` at a context of two live units, a dead slot, and `m`. -/
theorem d_tail₃ {Δ : LifeCtx} {a : Lifetime.Life} {S₁ : VTy} :
    CDerives Δ [⟨.unit, true⟩, ⟨.unit, true⟩, ⟨S₁, false⟩, ⟨.mut a TA, true⟩] (tailE 3)
      (.comp (.ret .unit)) :=
  .bind (.right (.right (.dead (.right .nil))))
    (.ret (.forgetMut (a := a) (A := TA) (.cons (.cons (.cons (.cons .nil))))))
    (.bind (.left (.right (.right (.dead (.left .nil)))))
      (.app (.left (.dead (.dead (.dead (.right .nil)))))
        (.force (.here (.cons (.cons (.cons (.cons .nil))))))
        (.there (.there (.there (.there (.here .nil))))))
      (.ret (.unitI (.drop pu (.cons (.drop pu (.drop pu (.cons (.cons .nil)))))))))

/-- `use m` at a context of three live units, a dead slot, and `m`. -/
theorem d_tail₄ {Δ : LifeCtx} {a : Lifetime.Life} {S₁ : VTy} :
    CDerives Δ [⟨.unit, true⟩, ⟨.unit, true⟩, ⟨.unit, true⟩, ⟨S₁, false⟩, ⟨.mut a TA, true⟩]
      (tailE 4) (.comp (.ret .unit)) :=
  .bind (.right (.right (.right (.dead (.right .nil)))))
    (.ret (.forgetMut (a := a) (A := TA) (.cons (.cons (.cons (.cons (.cons .nil)))))))
    (.bind (.left (.right (.right (.right (.dead (.left .nil))))))
      (.app (.left (.dead (.dead (.dead (.dead (.right .nil))))))
        (.force (.here (.cons (.cons (.cons (.cons (.cons .nil)))))))
        (.there (.there (.there (.there (.there (.here .nil)))))))
      (.ret (.unitI (.drop pu (.cons (.drop pu (.drop pu (.drop pu (.cons (.cons .nil))))))))))

theorem ctxNoEffT_of {Γ : Ctx VTy} (h : ∀ s ∈ Γ, s.live = true → NoEffT s.ty) : CtxNoEffT Γ := h

/-- **The program is in the fragment**, at the stack `[s@'x₂ reborrow, s@'x₁]` and the row
`{yield}`. -/
theorem d_branch {δ : LSub} {σ : LStack} {Δ : LifeCtx} {a : Lifetime.Life} :
    BComp (ℍ := ℍ) δ σ [yieldOp] Δ [⟨.mut a TA, true⟩] branchE .unit :=
  .letE (.right .nil)
    (.ret (.frozen (.sumI₂ (.unitI (.cons .nil)))
      (fun _ hs hl => by simp at hs; subst hs; simp at hl)
      (show NoEffT (.sum .unit .unit) from ⟨trivial, trivial⟩)
      (fun _ _ h => by simp [VFree] at h) (aboveAll_of_persistent rfl)))
    (.letE (.right (.right .nil))
      (.perform (o := yieldOp) (by simp [Row.find, yieldOp]) rfl rfl rfl
        (fun _ _ h => by simp [VFree, yieldOp] at h) (fun _ _ => .int)
        (.lit (.i32 1) (.cons (.cons .nil)))
        (fun _ hs hl => by simp at hs; rcases hs with rfl | rfl <;> simp at hl))
      (.case (.right (.left (.right .nil))) (.var (.there (.here (.cons .nil))))
        (.pure d_tail₃ (fun _ hs hl => by
            simp at hs; rcases hs with rfl | rfl | rfl | rfl <;> simp_all [NoEffT, yieldOp])
          trivial (fun _ _ h => by simp [VFree] at h) (aboveAll_of_persistent rfl))
        (.letE (.right (.right (.dead (.right .nil))))
          (.perform (o := yieldOp) (by simp [Row.find, yieldOp]) rfl rfl rfl
            (fun _ _ h => by simp [VFree, yieldOp] at h) (fun _ _ => .int)
            (.lit (.i32 2) (.cons (.cons (.cons (.cons .nil)))))
            (fun _ hs hl => by simp at hs; rcases hs with rfl | rfl | rfl | rfl <;> simp at hl))
          (.pure d_tail₄ (fun _ hs hl => by
              simp at hs; rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp_all [NoEffT, yieldOp])
            trivial (fun _ _ h => by simp [VFree] at h) (aboveAll_of_persistent rfl)))))

/-- **Law 2 at the stack `[s@'x₂ reborrow, s@'x₁]`, for every borrower of the fragment** holding
the reborrow's view and answering `()`: from the struct's owner, its `ewpTS` at `{yield}`, the
owner handed back. `law2_frag` with every hypothesis discharged once. -/
theorem law2_A (s : BoCa.Loc) {M : Expr}
    (hd : BComp (ℍ := ℍ) δA [e₂ s, e₁ s] [yieldOp] ΔA [⟨TM, true⟩] M .unit) (ls : List SRec) :
    Entails (owner s TA δA ls)
      (ewpTS (ℍ := ℍ) ls (substAll [Val.loc s] M) (opTable (Row.tab [yieldOp] δA))
        (fun ls v => owner s TA δA ls ⋆ ⌜v = Val.unit⌝)) := by
  intro ρ ho
  have hσ : MixedStack [e₂ s, e₁ s] :=
    .reborrow rfl rfl rfl rfl (.mutOther rfl (by simp) .nil)
  have hx : AllCross [e₂ s, e₁ s] (Row.tab [yieldOp] δA) := fun n i en _ e he => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl
  have ho' : ownersM (ℍ := ℍ) δA [e₂ s, e₁ s] ls ρ := by
    refine ⟨PMap.empty, ρ, compS_empty_left ρ, ?_, ρ, PMap.empty, ResU.comp_empty_right ρ, ?_,
      ⟨rfl, trivial⟩⟩
    · rw [if_pos (Reb_e₂ s)]; exact ⟨rfl, trivial⟩
    · rw [if_neg (not_Reb_e₁ s)]; exact ho
  have h := law2_frag (S := [yieldOp]) (by simp) (yield_linResume δA) (yield_local δA)
    (β := OrderDual.toDual 2) hσ hx
    (fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> exact TA_stratum)
    (fun e he v hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> cases hk)
    (Qa := fun _ v => ⌜v = Val.unit⌝) (fun _ _ _ _ _ h => h) (ds := [true, true])
    (bs := [OrderDual.toDual 4, OrderDual.toDual 3]) rfl rfl
    (fun a ha => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> decide)
    hd trivial (γ := [Val.loc s])
    (fun αs hlt hch => hΔ_A (hlt.imp fun _ _ => le_of_lt) hch s)
    (fun αs ls ρv hlt hch hv => hctx_view αs ls ρv hlt hch hv)
    (fun αs ls v ρ _ _ h => ⟨h, fun a _ => by rw [h.1]; exact ResU.inStratum_empty a⟩) ls ρ ho'
  have hw : withOwnersM (ℍ := ℍ) δA [e₂ s, e₁ s] (fun _ v => ⌜v = Val.unit⌝) =
      fun ls v => owner s TA δA ls ⋆ ⌜v = Val.unit⌝ := by
    simp only [withOwnersM, if_pos (Reb_e₂ s), if_neg (not_Reb_e₁ s)]; rfl
  rw [hw] at h
  exact h

/-- **A value computed before a stop, held across it, and a branch around a second stop.** The
generator lends `s` at `'x₁` and reborrows it at `'x₂`; it computes `c = inj₂ ()`, yields with
`c` and `m` in its frame, branches on `c` into a second yield or none, and uses `m` after. -/
theorem branch_spans (s : BoCa.Loc) (ls : List SRec) :
    Entails (owner s TA δA ls)
      (ewpTS (ℍ := ℍ) ls (substAll [Val.loc s] branchE) (opTable (Row.tab [yieldOp] δA))
        (fun ls v => owner s TA δA ls ⋆ ⌜v = Val.unit⌝)) :=
  law2_A s d_branch ls

/-! ### A closure that stops -/

/-- The row's computation at answer `()`. -/
abbrev C₀ : CTy := CTy.effOf [yieldOp] .unit

/-- `U(1 ⊸ F_{yield} 1)`. -/
abbrev thTy : VTy := .thunk (.arr .unit C₀)

/-- **The program.** `f = λ_. yield 2; yield 1; f (); use m`: the closure that stops is built
before the first stop, held across it, and called after it, stopping inside the callee. -/
abbrev closureE : Expr :=
  bindE (.val (.lam (yE 2))) (bindE (yE 1) (bindE (.app (.var 1) (.var 0)) (tailE 3)))

theorem d_tailB {Δ : LifeCtx} {a : Lifetime.Life} {S₀ S₁ : VTy} :
    CDerives Δ [⟨.unit, true⟩, ⟨S₀, false⟩, ⟨S₁, false⟩, ⟨.mut a TA, true⟩] (tailE 3)
      (.comp (.ret .unit)) :=
  .bind (.right (.dead (.dead (.right .nil))))
    (.ret (.forgetMut (a := a) (A := TA) (.cons (.cons (.cons (.cons .nil))))))
    (.bind (.left (.right (.dead (.dead (.left .nil)))))
      (.app (.left (.dead (.dead (.dead (.right .nil)))))
        (.force (.here (.cons (.cons (.cons (.cons .nil))))))
        (.there (.there (.there (.there (.here .nil))))))
      (.ret (.unitI (.drop pu (.cons (.drop pu (.cons (.cons (.cons .nil)))))))))

theorem perform_yield {δ : LSub} {σ : LStack} {Δ : LifeCtx} (n : UInt32) {Γ : Ctx VTy}
    (hΓ : Ctx.DeadP Γ) (hN : CtxNoEffT Γ) : BComp (ℍ := ℍ) δ σ [yieldOp] Δ Γ (yE n) .unit :=
  .perform (o := yieldOp) (by simp [Row.find, yieldOp]) rfl rfl rfl
    (fun _ _ h => by simp [VFree, yieldOp] at h) (fun _ _ => .int) (.lit (.i32 n) hΓ) hN

/-- A context of dead slots and live units holds no closure that stops. -/
theorem noEffT_units {Γ : Ctx VTy} (h : ∀ sl ∈ Γ, sl.live = true → sl.ty = .unit) :
    CtxNoEffT Γ := fun sl hs hl => by rw [h sl hs hl]; trivial

theorem d_closure {δ : LSub} {σ : LStack} {Δ : LifeCtx} {a : Lifetime.Life} :
    BComp (ℍ := ℍ) δ σ [yieldOp] Δ [⟨.mut a TA, true⟩] closureE .unit :=
  .letE (.right .nil)
    (.ret (.lamEff (perform_yield 2 (.drop pu (.cons .nil))
      (noEffT_units fun _ hs hl => by simp at hs; rcases hs with rfl | rfl <;> simp_all))))
    (.letE (.right (.right .nil)) (perform_yield 1 (.cons (.cons .nil))
      (noEffT_units fun _ hs hl => by simp at hs; rcases hs with rfl | rfl <;> simp_all))
      (.letE (.left (.left (.right .nil)))
        (.call (.right (.left (.dead .nil))) (.there (.here (.cons .nil)))
          (.here (.cons (.cons .nil))))
        (.pure d_tailB (fun _ hs hl => by
            simp at hs; rcases hs with rfl | rfl | rfl | rfl <;> simp_all [NoEffT])
          trivial (fun _ _ h => by simp [VFree] at h) (aboveAll_of_persistent rfl))))

/-- **A closure that stops, built before a stop and called after it.** The generator builds
`f = λ_. yield 2`, yields with `f` and `m` in its frame, calls `f` — which stops inside the callee
with both lends open — and uses `m` after. -/
theorem closure_stops_spans (s : BoCa.Loc) (ls : List SRec) :
    Entails (owner s TA δA ls)
      (ewpTS (ℍ := ℍ) ls (substAll [Val.loc s] closureE) (opTable (Row.tab [yieldOp] δA))
        (fun ls v => owner s TA δA ls ⋆ ⌜v = Val.unit⌝)) :=
  law2_A s d_closure ls

/-! ### A loop around a stop -/

/-- The step's argument, `(1 ⊕ !U(1 ⊸ F_{yield} 1)) ⊗ 1`. -/
abbrev stArgTy : VTy := .tensor (fixSelfTy .unit C₀) .unit

/-- `bounded_fix`'s argument, `step ⊗ (I32 ⊗ 1)`. -/
abbrev fxArgTy : VTy := .tensor (fixStepTy .unit C₀) (.tensor (.int .w32) .unit)

/-- **The loop's step**: `λp. let (self, a) = p in yield 3; case self of inj₁ _ ⇒ () |
inj₂ g ⇒ g a` — one yield per iteration, the next iteration through the self-reference. -/
abbrev stepBody : Expr :=
  .letpair (.var 0)
    (bindE (yE 3) (.case (.var 2) (.val .unit) (bindE (.var 0) (.app (.var 0) (.var 3)))))

/-- **The program.** The step, then `bounded_fix (step, (3, ()))`, then `use m`: the view `m` is
held in the frame across every iteration's stop. -/
abbrev loopE : Expr :=
  bindE (.val (.lam stepBody))
    (bindE (.val (.prim .boundedFix))
      (bindE (.pair (.var 1) (.pair (.val (Val.i32 3)) (.val .unit)))
        (bindE (.app (.var 1) (.var 0)) (tailE 4))))

theorem d_tailC {Δ : LifeCtx} {a : Lifetime.Life} {S₀ S₁ S₂ : VTy} :
    CDerives Δ [⟨.unit, true⟩, ⟨S₀, false⟩, ⟨S₁, false⟩, ⟨S₂, false⟩, ⟨.mut a TA, true⟩] (tailE 4)
      (.comp (.ret .unit)) :=
  .bind (.right (.dead (.dead (.dead (.right .nil)))))
    (.ret (.forgetMut (a := a) (A := TA) (.cons (.cons (.cons (.cons (.cons .nil)))))))
    (.bind (.left (.right (.dead (.dead (.dead (.left .nil))))))
      (.app (.left (.dead (.dead (.dead (.dead (.right .nil))))))
        (.force (.here (.cons (.cons (.cons (.cons (.cons .nil)))))))
        (.there (.there (.there (.there (.there (.here .nil)))))))
      (.ret (.unitI (.drop pu (.cons (.drop pu (.cons (.cons (.cons (.cons .nil))))))))))

theorem d_step {δ : LSub} {σ : LStack} {Δ : LifeCtx} {S₀ : VTy} :
    BComp (ℍ := ℍ) δ σ [yieldOp] Δ [⟨stArgTy, true⟩, ⟨S₀, false⟩] stepBody .unit :=
  .letpair (.left (.dead .nil)) (.var (.here (.cons .nil)))
    (.letE (.right (.right (.dead (.dead .nil))))
      (perform_yield 3 (.cons (.cons (.cons (.cons .nil))))
        (noEffT_units fun _ hs hl => by
          simp at hs; rcases hs with rfl | rfl | rfl | rfl <;> simp_all))
      (.case (.right (.right (.left (.dead (.dead .nil)))))
        (.var (.there (.there (.here (.cons (.cons .nil))))))
        (.ret (.unit (.drop pu (.drop pu (.drop pu (.cons (.cons (.cons .nil))))))))
        (.letE (.left (.right (.right (.dead (.dead (.dead .nil))))))
          (.ret (.bangE (.var (.here (.cons (.cons (.cons (.cons (.cons .nil)))))))))
          (.call (.left (.dead (.right (.right (.dead (.dead (.dead .nil)))))))
            (.here (.cons (.cons (.cons (.cons (.cons (.cons .nil)))))))
            (.there (.there (.skip pu (.here (.cons (.cons (.cons .nil)))))))))))

theorem d_loop {δ : LSub} {σ : LStack} {Δ : LifeCtx} {a : Lifetime.Life} :
    BComp (ℍ := ℍ) δ σ [yieldOp] Δ [⟨.mut a TA, true⟩] loopE .unit :=
  .letE (.right .nil)
    (.ret (.bangLamEff (fun _ hs hl => by simp at hs; subst hs; simp at hl) d_step))
    (.letE (.right (.right .nil)) (.ret (.bangE (.boundedFix (.cons (.cons .nil)))))
      (.letE (.right (.left (.right .nil)))
        (.ret (.pair (.dead (.left (.dead .nil))) (.var (.there (.here (.cons .nil))))
          (.pair (.dead (.dead (.dead .nil)))
            (.frozen (.lit (.i32 3) (.cons (.cons (.cons .nil))))
              (fun _ hs hl => by simp at hs; rcases hs with rfl | rfl | rfl <;> simp at hl)
              trivial (fun _ _ h => by simp [VFree] at h) (aboveAll_of_persistent rfl))
            (.unit (.cons (.cons (.cons .nil)))))))
        (.letE (.left (.left (.dead (.right .nil))))
          (.call (.right (.left (.dead (.dead .nil)))) (.there (.here (.cons (.cons .nil))))
            (.here (.cons (.cons (.cons .nil)))))
          (.pure d_tailC (fun _ hs hl => by
              simp at hs; rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp_all [NoEffT])
            trivial (fun _ _ h => by simp [VFree] at h) (aboveAll_of_persistent rfl)))))

/-- **A loop around a stop, the view held across every iteration.** The generator builds the
step, runs `bounded_fix (step, (3, ()))` — each iteration yields once with both lends open —
and uses `m` after the loop. -/
theorem loop_spans (s : BoCa.Loc) (ls : List SRec) :
    Entails (owner s TA δA ls)
      (ewpTS (ℍ := ℍ) ls (substAll [Val.loc s] loopE) (opTable (Row.tab [yieldOp] δA))
        (fun ls v => owner s TA δA ls ⋆ ⌜v = Val.unit⌝)) :=
  law2_A s d_loop ls

/-! ### Depth 3: a reborrow chain -/

/-- The reborrow of the reborrow, at `'x₃`. -/
abbrev e₃ (s : BoCa.Loc) : LEnt := ⟨s, 3, TA, .mut, tt⟩

/-- `'x₃ ⊏ 'x₂ ⊏ 'x₁ ⊏ ⊤`, `'b ⊏ ⊤`. -/
abbrev ΔC : LifeCtx := ΔA.extend 3 (.var 2)

theorem models_C (δ : LSub) (h5 : δ.find? 5 = some 1) {α₃ α₂ α₁ : Life} (h32 : α₃ < α₂)
    (h21 : α₂ < α₁) (h1 : α₁ < ⊤) : ΔC.Models (((δ.extend 1 α₁).extend 2 α₂).extend 3 α₃) := by
  intro x u hu
  by_cases hx : x = 3
  · subst hx
    simp only [ΔC, LifeCtx.find?, LifeCtx.extend, Lifetime.assocFind] at hu
    simp at hu; subst hu
    refine ⟨α₃, α₂, find?_extend_self _ _ _, ?_, h32⟩
    rw [Lifetime.Life.interp_var, find?_extend_ne _ _ (by decide), find?_extend_self]
    rfl
  · have hu' : ΔA.find? x = some u := by
      simp only [ΔC, LifeCtx.find?, LifeCtx.extend, Lifetime.assocFind] at hu ⊢
      rw [if_neg (Ne.symm hx)] at hu
      exact hu
    exact models_B δ h5 h21 h1 x u hu'

theorem hΔ_C {αs : List Life}
    (hlt : List.Forall₂ (· < ·) αs [OrderDual.toDual 5, OrderDual.toDual 4, OrderDual.toDual 3])
    (hch : List.IsChain (· < ·) αs) (s : BoCa.Loc) :
    ΔC.Models (extS δA [e₃ s, e₂ s, e₁ s] αs) := by
  match αs, hlt with
  | [α₃, α₂, α₁], .cons _ (.cons _ (.cons h₁ .nil)) =>
    have hc := List.isChain_cons_cons.mp hch
    have hc' := List.isChain_cons_cons.mp hc.2
    exact models_C δA rfl hc.1 hc'.1 (lt_trans h₁ (by decide))

/-- **The innermost reborrow's view**, the two outer views shadowed, rebuilds `m : Mut 'x₃ TA` at
every re-lend: the view is re-lendable, no part frozen. -/
theorem rctx_view₃ {s : BoCa.Loc} {αs : List Life} {ls : List SRec} {ρv : WRes}
    (hv : vwS δA [] [e₃ s, e₂ s, e₁ s] [true, true, true] αs ls ρv) :
    RCtx (ℍ := ℍ) δA [e₃ s, e₂ s, e₁ s] αs ls [⟨.mut (.var 3) TA, true⟩] [Val.loc s] ρv := by
  refine pure_sep_mk trivial ⟨ρv, PMap.empty, ResU.comp_empty_right ρv, ?_, ⟨rfl, trivial⟩⟩
  show RelendableS δA [] [e₃ s, e₂ s, e₁ s]
    (fun αs' ls' => vCE (ℍ := ℍ) none true (.mut (.var 3) TA) ls'
      (extS δA [e₃ s, e₂ s, e₁ s] αs') (Val.loc s)) αs ls ρv
  refine ⟨[true, true, true], PMap.empty, ρv, compS_empty_left ρv, hv,
    fun a _ => ResU.inStratum_empty a, fun ls' _ αs' hr ρv' τ hv' hc => ?_⟩
  rw [eq_of_compS_empty_left hc]
  match αs', hr.1 with
  | [α₃, α₂, α₁], _ =>
    obtain ⟨a, b, hcab, ha, hb⟩ := hv'
    obtain ⟨b₁, b₂, hcb, hb₁, hb₂⟩ := hb
    have hb₁' : b₁ = PMap.empty := by
      simp only [vis, List.mem_singleton, decide_true, Bool.not_true, Bool.and_false, vwE] at hb₁
      exact hb₁.1
    obtain ⟨b₃, b₄, hcb', hb₃, hb₄⟩ := hb₂
    have hb₃' : b₃ = PMap.empty := by
      simp only [vis, List.mem_cons, true_or, decide_true, Bool.not_true, Bool.and_false,
        vwE] at hb₃
      exact hb₃.1
    have hb₄' : b₄ = PMap.empty := hb₄.1
    subst hb₁' hb₃' hb₄'
    obtain rfl : b₂ = PMap.empty := eq_of_compS_empty_left hcb'
    obtain rfl : b = PMap.empty := eq_of_compS_empty_left hcb
    rw [ResU.CompS.functional hcab (ResU.comp_empty_right a)]
    have hview : viewP s TA δA α₃ ls' a := by simpa [vis, vwE] using ha
    have e : (fun ls₀ => vCE (ℍ := ℍ) none true TA ls₀ ((δA.extend 1 α₁).extend 2 α₂)) =
        (fun ls₀ => vCE (ℍ := ℍ) none true TA ls₀ δA) := funext fun ls₀ => by
      rw [vC_extend_of_not_free (by simp [VFree, Lifetime.Life.mentions]),
        vC_extend_of_not_free (by simp [VFree, Lifetime.Life.mentions])]
    exact mutView (x := 3) (by simp [VFree, Lifetime.Life.mentions])
      (show ptoMutS s α₃ ls' (fun ls₀ => vCE (ℍ := ℍ) none true TA ls₀
        ((δA.extend 1 α₁).extend 2 α₂)) a by rw [e]; exact hview)

theorem Reb_e₃ (s : BoCa.Loc) : Reb (e₃ s) [e₂ s, e₁ s] := by simp [Reb]

/-- **Law 2 at the depth-3 reborrow chain `[s@'x₃ reborrow, s@'x₂ reborrow, s@'x₁]`, for every
borrower of the fragment** holding the innermost reborrow's view and answering `()`. -/
theorem law2_C (s : BoCa.Loc) {M : Expr}
    (hd : BComp (ℍ := ℍ) δA [e₃ s, e₂ s, e₁ s] [yieldOp] ΔC [⟨.mut (.var 3) TA, true⟩] M .unit)
    (ls : List SRec) :
    Entails (owner s TA δA ls)
      (ewpTS (ℍ := ℍ) ls (substAll [Val.loc s] M) (opTable (Row.tab [yieldOp] δA))
        (fun ls v => owner s TA δA ls ⋆ ⌜v = Val.unit⌝)) := by
  intro ρ ho
  have hσ : MixedStack [e₃ s, e₂ s, e₁ s] :=
    .reborrow rfl rfl rfl rfl (.reborrow rfl rfl rfl rfl (.mutOther rfl (by simp) .nil))
  have hx : AllCross [e₃ s, e₂ s, e₁ s] (Row.tab [yieldOp] δA) := fun n i en _ e he => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> rfl
  have ho' : ownersM (ℍ := ℍ) δA [e₃ s, e₂ s, e₁ s] ls ρ := by
    refine ⟨PMap.empty, ρ, compS_empty_left ρ, ?_, PMap.empty, ρ, compS_empty_left ρ, ?_,
      ρ, PMap.empty, ResU.comp_empty_right ρ, ?_, ⟨rfl, trivial⟩⟩
    · rw [if_pos (Reb_e₃ s)]; exact ⟨rfl, trivial⟩
    · rw [if_pos (Reb_e₂ s)]; exact ⟨rfl, trivial⟩
    · rw [if_neg (not_Reb_e₁ s)]; exact ho
  have h := law2_frag (S := [yieldOp]) (by simp) (yield_linResume δA) (yield_local δA)
    (β := OrderDual.toDual 2) hσ hx
    (fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> exact TA_stratum)
    (fun e he v hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> cases hk)
    (Qa := fun _ v => ⌜v = Val.unit⌝) (fun _ _ _ _ _ h => h) (ds := [true, true, true])
    (bs := [OrderDual.toDual 5, OrderDual.toDual 4, OrderDual.toDual 3]) rfl rfl
    (fun a ha => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> decide)
    hd trivial (γ := [Val.loc s]) (fun αs hlt hch => hΔ_C hlt hch s)
    (fun αs ls ρv _ _ hv => ⟨ρv, PMap.empty, ResU.comp_empty_right ρv, noOwn_empty,
      rctx_view₃ hv⟩)
    (fun αs ls v ρ _ _ h => ⟨h, fun a _ => by rw [h.1]; exact ResU.inStratum_empty a⟩) ls ρ ho'
  have hw : withOwnersM (ℍ := ℍ) δA [e₃ s, e₂ s, e₁ s] (fun _ v => ⌜v = Val.unit⌝) =
      fun ls v => owner s TA δA ls ⋆ ⌜v = Val.unit⌝ := by
    simp only [withOwnersM, if_pos (Reb_e₃ s), if_pos (Reb_e₂ s), if_neg (not_Reb_e₁ s)]; rfl
  rw [hw] at h
  exact h

/-- **Depth 3, a reborrow chain**: the struct `s` lent at `'x₁`, reborrowed at `'x₂` and that
reborrow reborrowed at `'x₃`; the generator, holding the innermost view, runs the loop of
`loop_spans` — every iteration yielding with the three lends open — and uses the view after. -/
theorem chain3_loop_spans (s : BoCa.Loc) (ls : List SRec) :
    Entails (owner s TA δA ls)
      (ewpTS (ℍ := ℍ) ls (substAll [Val.loc s] loopE) (opTable (Row.tab [yieldOp] δA))
        (fun ls v => owner s TA δA ls ⋆ ⌜v = Val.unit⌝)) :=
  law2_C s d_loop ls

/-- **Depth 3, a reborrow chain**, the branch program of `branch_spans`. -/
theorem chain3_branch_spans (s : BoCa.Loc) (ls : List SRec) :
    Entails (owner s TA δA ls)
      (ewpTS (ℍ := ℍ) ls (substAll [Val.loc s] branchE) (opTable (Row.tab [yieldOp] δA))
        (fun ls v => owner s TA δA ls ⋆ ⌜v = Val.unit⌝)) :=
  law2_C s d_branch ls

end Law2.Inst

end
