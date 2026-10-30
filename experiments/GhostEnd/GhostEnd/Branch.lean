import GhostEnd.Typed
import GhostEnd.Instance

/-!
# GhostEnd — a borrower that branches around its yields, every hypothesis discharged

    withbor ℓ (Λ. λm. return (inj₁ ()) to c.
                      perform yield 1 to u. u;
                      case c { inj₁ z. z; perform yield 2 to u₂. u₂; N_f
                             | inj₂ z. z; N_f })

at the row `{yield : I32 ↠ 1}`, linear and resuming. `c` is data computed before the first
yield and held across it; the branch on it decides whether a second yield follows. `m` is held
across every yield and used by `N_f` (`forget m`, then `return ()` boxed at `'x`).

Every piece is typed by the kernel's rules, and `RBody` is derived from those typings rule by
rule (`rbody_let`, `rbody_perform`, `rbody_seq`, `rbody_case`, `rbody_ret`). `branch_spans_yields`
is `withbor_of_rbody` with every hypothesis discharged.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd.Branch
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (performE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd.Instance (yieldOp)

/-- The borrow's slot here: `m : Mut 'x 1`, `'x = 0`. -/
abbrev mS (ml : Bool) : Slot VTy := mSlot 0 .unit ml

/-- A context of dead slots. -/
def deadOf (Ds : List VTy) : Ctx VTy := Ds.map fun A => ⟨A, false⟩

theorem splitDR : ∀ Ds : List VTy,
    Ctx.SplitP (deadOf Ds ++ [mS true]) (deadOf Ds ++ [mS false]) (deadOf Ds ++ [mS true])
  | [] => .right .nil
  | _ :: Ds => .dead (splitDR Ds)

theorem splitDL : ∀ Ds : List VTy,
    Ctx.SplitP (deadOf Ds ++ [mS true]) (deadOf Ds ++ [mS true]) (deadOf Ds ++ [mS false])
  | [] => .left .nil
  | _ :: Ds => .dead (splitDL Ds)

theorem deadPD : ∀ Ds : List VTy, Ctx.DeadP (deadOf Ds ++ [mS false])
  | [] => .cons .nil
  | _ :: Ds => .cons (deadPD Ds)

theorem deadD : ∀ Ds : List VTy, Ctx.Dead (deadOf Ds ++ [mS false])
  | [] => .cons .nil
  | _ :: Ds => .cons (deadD Ds)

theorem soloPD : ∀ Ds : List VTy, Ctx.SoloP (deadOf Ds ++ [mS true]) Ds.length (.mut (.var 0) .unit)
  | [] => .here .nil
  | _ :: Ds => .there (soloPD Ds)

/-- `return forget to fg. fg m to z. return z`, `m` past `k` dead slots. -/
def nfAt (k : Nat) : Expr := bindE forget (bindE (.app (.var 0) (.var (k + 1))) (.var 0))

/-- `N_f` typed past dead slots: `Δ₁; D, m : Mut 'x 1 ⊢ N_f : F(['x] 1)`. -/
theorem d_nfAt (Ds : List VTy) :
    CDerives Δ₁ (deadOf Ds ++ [mS true]) (nfAt Ds.length) (.comp (.ret (.box (.var 0) .unit))) :=
  .bind (splitDR Ds) (.ret (.forgetMut (a := .var 0) (A := .unit) (deadPD Ds)))
    (.bind (.left (splitDL Ds))
      (.app (.left (splitDR Ds)) (.force (.here (deadPD Ds))) (.there (soloPD Ds)))
      (.ret (.boxI (.var (.here (.cons (deadPD Ds))))
        (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) .unit (.cons (deadD Ds))))))

/-- `perform yield k`. -/
def yieldE (k : UInt32) : Expr := performE (opArgE yieldOp.n yieldOp.i (.val (Val.i32 k)))

abbrev cT : VTy := .sum .unit .unit

/-- The inj₂ branch: `z; N_f`. -/
def br₂ : Expr := .seq (.var 0) (nfAt 3)

/-- The inj₁ branch: `z; perform yield 2 to u₂. u₂; N_f`. -/
def br₁ : Expr := .seq (.var 0) (bindE (yieldE 2) (.seq (.var 0) (nfAt 4)))

/-- `u; case c { … }`. -/
def afterYield : Expr := .seq (.var 0) (.case (.var 1) br₁ br₂)

/-- The borrower's body. -/
def body : Expr := bindE (.val (Val.inj₁ Val.unit)) (bindE (yieldE 1) afterYield)

/-! ### Its pieces, rule by rule -/

theorem hbx : (LifeCtx.empty.meetOfDom).mentions 0 = false := by decide
theorem hΔx : ∀ y u, LifeCtx.empty.find? y = some u → u.mentions 0 = false := fun y u h => by
  simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind] at h

theorem hS : Row.Resume [yieldOp] 0 := by
  intro o ho
  simp only [List.mem_singleton] at ho
  subst ho
  exact ⟨by decide, by decide, rfl, rfl, by simp [VFree, yieldOp], fun _ _ => .int⟩

theorem hT : ¬ VFree 0 VTy.unit := by simp [VFree]

theorem hf : Row.find [yieldOp] yieldOp.n yieldOp.i = some yieldOp := by
  simp [Row.find, yieldOp]

/-- `perform yield k` at a dead context. -/
theorem rb_yield (Ds : List VTy) (k : UInt32) :
    RBody LifeCtx.empty 0 LifeCtx.empty.meetOfDom .unit [yieldOp] (deadOf Ds) false (yieldE k)
      .unit :=
  rbody_perform hbx hΔx hS hf (fundamentalC (.lit (.i32 k) (deadPD Ds)))

/-- `N_f` past dead slots. -/
theorem rb_nf (Ds : List VTy) :
    RBody LifeCtx.empty 0 LifeCtx.empty.meetOfDom .unit [yieldOp] (deadOf Ds) true
      (nfAt Ds.length) (.box (.var 0) .unit) :=
  rbody_ret hbx hΔx (fundamentalC (d_nfAt Ds))

abbrev RB (Γ : Ctx VTy) (ml : Bool) (E : Expr) : Prop :=
  RBody LifeCtx.empty 0 LifeCtx.empty.meetOfDom .unit [yieldOp] Γ ml E (.box (.var 0) .unit)

/-- `u₂; N_f`, `u₂` live in front of three dead slots. -/
theorem rb_tail₁ :
    RB [⟨.unit, true⟩, ⟨.unit, false⟩, ⟨.unit, false⟩, ⟨cT, false⟩] true (.seq (.var 0) (nfAt 4)) :=
  rbody_seq hbx hΔx (Γ₁ := [⟨.unit, true⟩, ⟨.unit, false⟩, ⟨.unit, false⟩, ⟨cT, false⟩])
    (Γ₂ := deadOf [.unit, .unit, .unit, cT]) (ml₁ := false)
    (.left (.dead (.dead (.dead (.right .nil))))) rfl (fun _ => rfl)
    (fundamentalC (.var (.here (.cons (.cons (.cons (.cons .nil)))))))
    (rb_nf [.unit, .unit, .unit, cT])

theorem rb_br₁ : RB [⟨.unit, true⟩, ⟨.unit, false⟩, ⟨cT, false⟩] true br₁ := by
  refine rbody_seq hbx hΔx (Γ₁ := [⟨.unit, true⟩, ⟨.unit, false⟩, ⟨cT, false⟩])
    (Γ₂ := deadOf [.unit, .unit, cT]) (ml₁ := false)
    (.left (.dead (.dead (.right .nil)))) rfl (fun _ => rfl)
    (fundamentalC (.var (.here (.cons (.cons (.cons .nil)))))) ?_
  exact rbody_let hbx hΔx hT hS (Γ₁ := deadOf [.unit, .unit, cT]) (Γ₂ := deadOf [.unit, .unit, cT])
    (ml₁ := false) (ml₂ := true) (A₁ := .unit)
    (.dead (.dead (.dead (.right .nil)))) rfl rfl (fun _ => ⟨rfl, rfl⟩) (fun h => absurd h (by decide))
    (fun s hs hl => by simp [deadOf] at hs; rcases hs with rfl | rfl | rfl <;> simp at hl)
    (rb_yield [.unit, .unit, cT] 2) rb_tail₁

theorem rb_br₂ : RB [⟨.unit, true⟩, ⟨.unit, false⟩, ⟨cT, false⟩] true br₂ :=
  rbody_seq hbx hΔx (Γ₁ := [⟨.unit, true⟩, ⟨.unit, false⟩, ⟨cT, false⟩])
    (Γ₂ := deadOf [.unit, .unit, cT]) (ml₁ := false)
    (.left (.dead (.dead (.right .nil)))) rfl (fun _ => rfl)
    (fundamentalC (.var (.here (.cons (.cons (.cons .nil))))))
    (rb_nf [.unit, .unit, cT])

theorem rb_after : RB [⟨.unit, true⟩, ⟨cT, true⟩] true afterYield := by
  refine rbody_seq hbx hΔx (Γ₁ := [⟨.unit, true⟩, ⟨cT, false⟩]) (Γ₂ := [⟨.unit, false⟩, ⟨cT, true⟩])
    (ml₁ := false) (ml₂ := true)
    (.left (.right (.right .nil))) rfl (fun _ => rfl)
    (fundamentalC (.var (.here (.cons (.cons .nil))))) ?_
  exact rbody_case hbx hΔx (Γs := [⟨.unit, false⟩, ⟨cT, true⟩]) (Γb := [⟨.unit, false⟩, ⟨cT, false⟩])
    (mls := false) (mlb := true) (A := .unit) (B := .unit)
    (.dead (.left (.right .nil))) rfl (fun _ => rfl)
    (fundamentalC (.var (.there (.here (.cons .nil))))) rb_br₁ rb_br₂

/-- `c` is data that outlives `'x`: it may span the yield. -/
theorem safe_c : StopSafe LifeCtx.empty 0 LifeCtx.empty.meetOfDom [⟨cT, true⟩] := by
  intro s hs _
  simp only [List.mem_singleton] at hs
  subst hs
  exact ⟨by simp [VFree], .sum .unit .unit⟩

theorem rb_mid : RB [⟨cT, true⟩] true (bindE (yieldE 1) afterYield) :=
  rbody_let hbx hΔx hT hS (Γ₁ := [⟨cT, false⟩]) (Γ₂ := [⟨cT, true⟩]) (ml₁ := false) (ml₂ := true)
    (A₁ := .unit) (.right (.right .nil)) rfl rfl (fun _ => ⟨rfl, rfl⟩)
    (fun h => absurd h (by decide)) safe_c (rb_yield [cT] 1) rb_after

theorem rb_body : RB [] true body :=
  rbody_let hbx hΔx hT hS (Γ₁ := []) (Γ₂ := []) (ml₁ := false) (ml₂ := true) (A₁ := cT)
    (.right .nil) rfl rfl (fun _ => ⟨rfl, rfl⟩) (fun h => absurd h (by decide))
    (fun _ hs => by simp at hs)
    (rbody_ret hbx hΔx (fundamentalC (.ret (.sumI₁ (.unitI (.cons .nil)))))) rb_mid

/-- **A borrower that branches around its yields.** From `ℓ ↦ v ⋆ 𝒱⟦1⟧(v)`, the program is in
`𝒞⟦F_{yield} (Ref 1 ⊗ 1)⟧`, at every assignment and record list. -/
theorem branch_spans_yields (δ : LSub) (l : BoCa.Loc) (v : Val) (ls : List SRec) :
    Entails (ptoOwn l v ⋆ vC true .unit ls δ v)
      (cC (CTy.effOf [yieldOp] (.tensor (.ref .unit) .unit)) ls δ
        (.app (.app withbor (.val (.loc l))) (.val ⟨.lam (.lam body), .lam⟩))) := by
  have hδ : LifeCtx.empty.Models δ := fun x u h => by
    simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind] at h
  obtain ⟨β, hβ⟩ : ∃ β, LifeCtx.empty.meetOfDom.interp δ = some β :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf LifeCtx.empty.entries)
  refine withbor_of_rbody hδ hβ hT (by simp [VFree]) (βP := ⊤) ?_ (by decide) (by decide) rb_body l v ls
  intro ls w σ h
  rw [h.1]; exact ResU.inStratum_empty _

end GhostEnd.Branch
