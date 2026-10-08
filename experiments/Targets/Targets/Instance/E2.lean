import Targets.Instance.E5

/-!
# The Instance — E2 (higher-order polymorphism) at `J₁`

**E2d** (`e2d_J₁`): `sumGen = λgen. handle yield {return _ ⇒ ff; yield (x, k) ⇒ resume k () to r.
case x of inl _ ⇒ r | inr _ ⇒ tt} (gen ())` is typed once, at
`U(∀ρ:any. U(1 ⊸ F_{yield ⊙ ρ} 1) ⊸ F_ρ bool)` (`derV_sumGen_J₁`): at each instance its handler is
typed at the first matches of the row without `yield` (`Row.firsts`, `Row.dropName`).  Its one typing
serves a generator at every `yield ⊙ ε`, the use at `ε` (`polyUseOpen_sumGen_J₁`).  E2d's body is
typed (`der_body2d_J₁`) and runs to `(tt, inr ())` (`runsTo_prog2d`): three catches around their
cells, the second inside the first's clause, and the raise passing `sumGen`'s reinstalled handler.
The clause's `[let]` holds `x : bool` across the resume; at a row with an `unr` operation `[let]`
requires the continuation's context persistent (`!`), which `bool` is not, so `sumGen` is typed at a
context with no `unr` operation (`NoUnr`, which `ΞA` meets).  `[Core σ=[]]`

**E2a, E2b, E2c** are not derived here, and no obstruction is machine-checked.  `twice`
(E2a) uses its argument `h` twice, so `h`'s slot is at `!U C`; Core's `force` reads a slot at
`U C` only (`CDerivesAt.force`), and no rule forces a `!U C` slot.  `compose` (E2b) holds `g₂`
across `g₁ () to _.`, a `[let]` at the callbacks' row: at a row with a non-linear operation that
continuation's context must drop (`Row.Weak → Ctx.Drops`), so `g₂` is at `!U C`, and is forced.
`retryP` (E2c) calls `pol` from its handler's clause, whose context's live slots are persistent
(`[handle]` at a value form), so `pol` is at `!U C`, and is forced.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Head Kont performE raiseE hndE hndVal opPayload kappaCell kappaCBody freeE
  kappaAt capTag)
open BoCa.Lifetime (LifeCtx)
open Targets (EffCtx orowRF orowAlg ORow RowAt rowAt_nil CDerivesAt lookEnd RowEnv)

/-! ### A row's first matches -/

/-- The row with every entry shadowed by an earlier one of its name and index removed. -/
def Row.firsts : Row → Row
  | [] => []
  | o :: S => o :: (Row.firsts S).filter (fun o' => !(o'.n == o.n && o'.i == o.i))

/-- Filtering a row by a test that keeps every entry of the name `n` and index `i` keeps their
first match. -/
theorem find_filter_ne {n i : UInt32} {p : OpSig → Bool}
    (hp : ∀ o, o.n = n → o.i = i → p o = true) :
    ∀ S : Row, Row.find (S.filter p) n i = Row.find S n i
  | [] => rfl
  | o :: S => by
      unfold Row.find at *
      by_cases ho : o.n = n ∧ o.i = i
      · rw [List.filter_cons_of_pos (hp o ho.1 ho.2), List.find?_cons, List.find?_cons]
        have hk : decide (n = o.n ∧ i = o.i) = true := by simp [ho.1, ho.2]
        rw [hk]
      · by_cases hpo : p o = true
        · rw [List.filter_cons_of_pos hpo, List.find?_cons, List.find?_cons]
          split
          · rfl
          · exact find_filter_ne hp S
        · rw [List.filter_cons_of_neg hpo, List.find?_cons]
          have hk : decide (n = o.n ∧ i = o.i) = false := by
            simp only [decide_eq_false_iff_not, not_and]
            intro h1 h2; exact ho ⟨h1.symm, h2.symm⟩
          rw [hk]
          exact find_filter_ne hp S

/-- A row's first matches find what the row finds. -/
theorem find_firsts : ∀ (S : Row) (n i : UInt32), Row.find (Row.firsts S) n i = Row.find S n i
  | [], _, _ => rfl
  | o :: S, n, i => by
      unfold Row.firsts
      unfold Row.find
      rw [List.find?_cons, List.find?_cons]
      split
      · rfl
      · rename_i h
        have hne : ¬ (n = o.n ∧ i = o.i) := by simpa using h
        have := find_filter_ne (n := n) (i := i)
          (p := fun o' => !(o'.n == o.n && o'.i == o.i))
          (fun o' h1 h2 => by
            subst h1; subst h2
            simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
            by_contra hc
            simp only [not_or, not_not] at hc
            exact hne ⟨hc.1, hc.2⟩) (Row.firsts S)
        unfold Row.find at this
        rw [this]
        exact find_firsts S n i

/-- Each of a row's first matches is what the row finds at its name and index. -/
theorem mem_firsts : ∀ {S : Row} {o : OpSig}, o ∈ Row.firsts S → Row.find S o.n o.i = some o
  | [], _, h => by simp [Row.firsts] at h
  | o' :: S, o, h => by
      unfold Row.firsts at h
      rcases List.mem_cons.mp h with rfl | h
      · simp [Row.find]
      · obtain ⟨hm, hp⟩ := List.mem_filter.mp h
        have hf := mem_firsts hm
        unfold Row.find at hf ⊢
        rw [List.find?_cons]
        have hk : decide (o.n = o'.n ∧ o.i = o'.i) = false := by
          simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hp
          simp only [decide_eq_false_iff_not, not_and]
          intro h1 h2
          rcases hp with hp | hp
          · exact hp (by rw [h1])
          · exact hp (by rw [h2])
        rw [hk]
        exact hf

theorem mem_of_mem_firsts {S : Row} {o : OpSig} (h : o ∈ Row.firsts S) : o ∈ S :=
  (Row.find_mem (mem_firsts h)).1

theorem rowLe_firsts (S : Row) : RowLe (Row.firsts S) S := by
  intro n i o h
  rwa [find_firsts] at h

theorem rowLe_to_firsts (S : Row) : RowLe S (Row.firsts S) := by
  intro n i o h
  rwa [find_firsts]

/-- **No operation of the context is `unr`.** -/
def NoUnr (Ξ : EffCtx) : Prop := ∀ n, ∀ p ∈ Ξ n, p.1 ≠ .unr

theorem noUnr_ΞA : NoUnr ΞA := by
  intro n p hp
  rcases ΞA_cases n with h0 | h0
  · rw [h0] at hp; simp at hp
  · simp only [eSigs, List.mem_cons, List.mem_nil_iff, or_false] at h0
    rcases h0 with h0 | h0 | h0 | h0 | h0 | h0 <;> rw [h0] at hp <;> simp at hp <;> rw [hp] <;>
      decide

/-- At a context with no `unr` operation, a tied row's first matches have no `unr` operation. -/
theorem not_unr_firsts {Ξ : EffCtx} (hX : NoUnr Ξ) {S : Row} (hS : RowAt Ξ S) :
    ¬ (Row.firsts S).Unr := by
  rintro ⟨o, ho, hq⟩
  obtain ⟨-, -, hget⟩ := hS _ _ _ (mem_firsts ho)
  exact hX o.n _ (List.mem_of_getElem? hget) hq

/-! ### `sumGen`, as our instance writes it -/

/-- `yield (x, k) ⇒ resume k () to r. case x of inl _ ⇒ r | inr _ ⇒ tt`. -/
def sgClE : Expr :=
  .lam (.letpair (.var 0) (bindE (resumeE (.var 0) .unit) (.case (.var 2) (.var 1) (.inj₂ .unit))))

/-- `sumGen`'s handler: `return _ ⇒ ff`, and its clause. -/
def sgH : Expr := .pair (.lam (.inj₁ .unit)) (clausesE [sgClE])

theorem isVal_sgH : IsVal sgH := .pair .lam (.pair .lam .unit)

/-- `sumGen` at the name `ny` and the tags `qs`. -/
def sumGenE (ny : UInt32) (qs : Expr) : Expr :=
  .lam ((handleK ny qs (.lam (.inj₁ .unit)) [sgClE]).plug (appE (.var 0) .unit))

/-- `sumGen`'s polymorphic body, at the generator's row `S` before the row variable:
`U(1 ⊸ F_{S ⊙ ρ} 1) ⊸ F_ρ bool`. -/
def sgC (S : Row) : OCTy :=
  .arr (.thunk (.arr .unit (effAt S (OVTy.ofV .unit)))) (effAt [] (OVTy.ofV boolT))

theorem sgC_den (S : Row) (η : RowEnv) (r : Row) :
    (sgC S).den (Function.update η ρ₀ r) =
      .arr (.thunk (.arr .unit (CTy.effOf (S ++ r) .unit))) (CTy.effOf r boolT) := by
  simp [sgC, effAt, OCTy.den, OVTy.den, OVTy.den_ofV]

theorem sgC_rFree (S : Row) : (sgC S).RFree :=
  ⟨OCTy.rFree_ofC (.arr .unit (.ret .unit)), OVTy.rFree_ofV boolT⟩

section Typing
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

theorem sumGen_val (ly : (orowAlg Ξ).Lab) : ((𝕁).sumGen ly).1 = sumGenE ly.1 (qsOf Ξ ly.1) := rfl

/-- **`sumGen`'s clause** at the row `S`: its `[let]` holds `x : bool` across the resume, so `S`
has no `unr` operation. -/
theorem d_sgCl {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (S : Row) (hU : ¬ S.Unr) :
    CDerivesAt Ξ Δ Γ sgClE (.val (clauseTy S boolT (.aff, boolT, .unit))) := by
  rw [clauseTy_resuming rfl]
  refine d_lamBang hΓ (.tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_)
  refine .effLet (A := boolT) (.left (.right (.dead (deadSplit hΓ)))) (fun _ => ?_)
    (fun h => absurd h hU) ?_ ?_
  · intro s hs hl
    simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | rfl | hs
    · cases hl
    · exact .sum .unit .unit
    · cases hl
    · exact dead_noLive (P := fun s => s.ty.Drop) hΓ s hs hl
  · refine .bind (.right (.dead (.dead (deadSplit hΓ))))
      (.ret (.unitI (.cons (.cons (.cons hΓ.toP))))) ?_
    exact d_kResume (Γ := ⟨boolT, false⟩ :: ⟨.tensor boolT (kTy S boolT .aff .unit), false⟩ :: Γ)
      (.cons (.cons hΓ)) (q := .aff) (by decide)
  · refine .sumE (.right (.dead (.left (.dead (deadSplit hΓ)))))
      (.var (.there (.there (.here (.cons hΓ.toP))))) ?_ ?_
    · exact .effSub (rowLe_nil S) (.ret (.var (.skip rfl (.here (.cons (.cons (.cons hΓ.toP)))))))
    · exact .effSub (rowLe_nil S) (.ret (.sumI₂ (.unitI (.drop rfl (.drop rfl
        (.cons (.cons (.cons hΓ.toP))))))))

theorem d_sgH {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (S : Row) (hU : ¬ S.Unr) :
    CDerivesAt Ξ Δ Γ sgH
      (.val (.tensor (retTy S .unit boolT) (clausesTy S boolT [(.aff, boolT, .unit)]))) :=
  .tensorI (deadSplit hΓ) (d_lamBang hΓ (.effSub (rowLe_nil S) (.ret (.sumI₁ (.unitI
    (.drop rfl hΓ.toP))))))
    (.tensorI (deadSplit hΓ) (d_sgCl hΓ S hU) (.unitI hΓ.toP))

theorem dropName_rowOf_append (l : (orowAlg Ξ).Lab) (r : Row) :
    Row.dropName l.1 (rowOf l ++ r) = Row.dropName l.1 r := by
  unfold Row.dropName
  rw [List.filter_append]
  have : (rowOf l).filter (fun o => o.n != l.1) = [] := by
    rw [List.filter_eq_nil_iff]
    intro o ho
    simp [mem_ofEff_n ho]
  rw [this, List.nil_append]

/-- **`sumGen` at an instance**: the handler at the first matches of the row without `yield`. -/
theorem d_sumGen {ly : (orowAlg Ξ).Lab} (hly : Ξ ly.1 = [(.aff, boolT, .unit)]) (hX : NoUnr Ξ)
    {r : Row} (hr : RowAt Ξ r) {Δ : LifeCtx} :
    CDerivesAt Ξ Δ [] (sumGenE ly.1 (qsOf Ξ ly.1))
      (.comp (.arr (.thunk (.arr .unit (CTy.effOf (rowOf ly ++ r) .unit))) (CTy.effOf r boolT))) := by
  have hSr : RowLe (Row.firsts (Row.dropName ly.1 r)) r := fun n i o h =>
    rowLe_dropName ly.1 r n i o (rowLe_firsts _ n i o h)
  have hSat : RowAt Ξ (Row.firsts (Row.dropName ly.1 r)) := Targets.rowAt_of_le hSr hr
  have hcb : RowLe (rowOf ly ++ r)
      (Row.ofEff ly.1 [(.aff, boolT, .unit)] 0 ++ Row.firsts (Row.dropName ly.1 r)) := by
    have h₁ := rowLe_ofEff_dropName (rowAt_rowOf_append ly hr) ly.1
    rw [dropName_rowOf_append, hly] at h₁
    intro n i o h
    have h' := h₁ n i o h
    rw [Row.find_append] at h' ⊢
    rwa [find_firsts]
  refine .lam (.effSub hSr ?_)
  refine d_handleL ly hly hSat (fun o ho => ne_of_mem_dropName o (mem_of_mem_firsts ho)) isVal_sgH
    (d_sgH (kill_dead _) _ (not_unr_firsts hX (rowAt_dropName hr ly.1))) ?_
  exact .effSub hcb (d_callVar0 .nil)

/-- **E2d: `sumGen` is typed once**, at `U(∀ρ:any. U(1 ⊸ F_{yield ⊙ ρ} 1) ⊸ F_ρ bool)`, at a context
with no `unr` operation. -/
theorem derV_sumGen_J₁ {ly : (orowAlg Ξ).Lab} (hly : Ξ ly.1 = [(.aff, boolT, .unit)])
    (hX : NoUnr Ξ) : (𝕁).derV [] ((𝕁).sumGen ly) (polyTy (sgC (rowOf ly))) := by
  have hcl : closedAt 0 (sumGenE ly.1 (qsOf Ξ ly.1)) = true := by
    simpa using closedAt_of_derives (d_sumGen (Δ := LifeCtx.empty) hly hX (rowAt_nil Ξ)).toCDerives
  exact derV_poly_J₁ (b := (handleK ly.1 (qsOf Ξ ly.1) (.lam (.inj₁ .unit)) [sgClE]).plug
    (appE (.var 0) .unit)) (sgC_rFree _) trivial hcl fun r η _ hrt => by
      rw [sgC_den]; exact d_sumGen hly hX hrt

/-- A row that does not admit `l` has no operation of `l`'s name. -/
theorem names_of_lacks {ε : ORow} {l : (orowAlg Ξ).Lab} (h : (𝕁).Lacks ε l) :
    ∀ o ∈ ε.ops, o.n ≠ l.1 := by
  intro o ho hn
  refine h o.i.toNat ⟨o.i.toNat_lt, fun η => ?_⟩
  show (Row.find (ε.ops ++ _) l.1 (UInt32.ofNat o.i.toNat)).isSome
  rw [UInt32.ofNat_toNat]
  unfold Row.find
  rw [List.find?_isSome]
  exact ⟨o, List.mem_append_left _ ho, by simp [hn]⟩

/-- **E2d's schema at `J₁`**: the one typing of `sumGen` serves a generator at every row `yield ⊙ ε`,
`ε` without `yield`, the use at `ε`. -/
theorem polyUseOpen_sumGen_J₁ (hΞ : Ξ.NU) (ly : (orowAlg Ξ).Lab) :
    (𝕁).PolyUseOpen [polyTy (sgC (rowOf ly))] ly (fun g => (𝕁).call ((𝕁).var 0) g)
      (𝕁).UnitT (𝕁).bool := by
  intro ε ε' M hlack hcomp hM
  have hε' : ε' = ⟨rowOf ly ++ ε.ops, ε.tail⟩ := by
    have : (orowAlg Ξ).comp ((orowAlg Ξ).lift ly) ε = some ⟨rowOf ly ++ ε.ops, ε.tail⟩ := rfl
    exact (Option.some.inj (hcomp.symm.trans this))
  subst hε'
  have hops := names_of_lacks hlack
  obtain ⟨S, A', hS, hSt⟩ := hM.1 (fun _ => []) (envAt_nil Ξ)
  have hS' : CTy.effOf (orowRF.den Ξ ⟨rowOf ly ++ ε.ops, ε.tail⟩ (J₁.env Ξ (fun _ => [])))
      ((OVTy.ofV .unit).den (fun _ => [])) = CTy.effOf S A' := hS
  obtain ⟨hSeq, -⟩ := effOf_inj hS'
  have hat : RowAt Ξ ε.ops := by
    intro n i o hf
    obtain ⟨hmem, hn, -⟩ := Row.find_mem hf
    have hne : n ≠ ly.1 := by rw [← hn]; exact hops o hmem
    apply hSt n i o
    rw [← hSeq]
    show Row.find ((rowOf ly ++ ε.ops) ++ _) n i = some o
    rw [List.append_assoc, Row.find_append, rowOf, Targets.find_ofEff_other _ hne, Option.none_or,
      Row.find_append, hf, Option.some_or]
  exact der_callPoly_J₁ (Cp := sgC (rowOf ly)) (A := .unit) (B := boolT) hΞ (sgC_rFree _) trivial
    unitT_not_loop (fun η => by rw [sgC_den]; simp [List.append_assoc]) hM
    (tiedAt_F (fun _ => rfl) hat _)

end Typing

/-! ### `prog2d` -/

/-- `λ_. yield ff; yield tt`. -/
def gen1E (ny : UInt32) : Expr :=
  .lam (bindE (performE (opArgE ny 0 (.inj₁ .unit))) (performE (opArgE ny 0 (.inj₂ .unit))))

/-- `λ_. yield ff; raise exn ()`. -/
def gen2E (ny ne : UInt32) : Expr :=
  .lam (bindE (performE (opArgE ny 0 (.inj₁ .unit))) (raiseE (opArgE ne 0 .unit)))

/-- E2d's body with `s` filled by `W`. -/
def body2dW (W : Expr) (ny ne : UInt32) (qe : Expr) : Expr :=
  bindE (appE W (gen1E ny))
    (bindE ((handleK ne qe (.lam (.inj₁ (.var 0))) [.lam (.inj₂ .unit)]).plug (appE W (gen2E ny ne)))
      (.pair (.var 1) (.var 0)))

/-- `sumGen`'s handler at the name `ny`, at the affine `yield`. -/
def sgHV (ny : UInt32) : Val :=
  hndVal ny (qualsVal [.aff]) ⟨.lam (.inj₁ .unit), .lam⟩ ⟨clausesE [sgClE], .pair .lam .unit⟩

/-- E2d's rest after `s gen1`. -/
def r2d (ny ne : UInt32) (qe : Expr) : Expr :=
  bindE ((handleK ne qe (.lam (.inj₁ (.var 0))) [.lam (.inj₂ .unit)]).plug
    (appE (sumGenE ny (qualsVal [.aff]).1) (gen2E ny ne))) (.pair (.var 1) (.var 0))

theorem s2d_A (ny ne : UInt32) (qe : Qual) :
    lookEnd 4 (body2dW (sumGenE ny (qualsVal [.aff]).1) ny ne (qualsVal [qe]).1) =
      (bindK (r2d ny ne (qualsVal [qe]).1)).plug (hndE (sgHV ny)
        ((bindK (performE (opArgE ny 0 (.inj₂ .unit)))).plug
          (performE (.val (opPayload ny 0 ⟨.inj₁ .unit, .inj₁ .unit⟩))))) := by
  rfl

/-- The first catch's continuation inside the handler: the second yield. -/
def k2d1 (ny : UInt32) : Kont := bindK (performE (opArgE ny 0 (.inj₂ .unit)))

/-- The clause's frame after the resume, at the payload `x`. -/
def sgFr (x : Expr) : Kont := bindK (.case x (.var 1) (.inj₂ .unit))

/-- Around the allocation of `κ`'s cell, after the catch of `yield v` in `K`. -/
def sgKA (ny : UInt32) (v : Val) (K : Kont) : Kont :=
  .appR sgClE (.pairR v (.appR (.lam (kappaCBody true ny (sgHV ny) K)) .hole))

/-- Around the release of `κ`'s cell. -/
def sgKF (ny : UInt32) (K : Kont) : Kont :=
  Kont.appL (Kont.seq .hole (kResV (sgHV ny) K)) Val.unit

/-- E2d's toResult frame. -/
def tr2dK (ne : UInt32) (qe : Expr) : Kont :=
  handleK ne qe (.lam (.inj₁ (.var 0))) [.lam (.inj₂ .unit)]

/-- The pair's frame after `s gen1` answered `tt`. -/
def pr2dK : Kont := bindK (.pair (.inj₂ .unit) (.var 0))

theorem s2d_B (ny ne : UInt32) (qe : Expr) (ℓ : Loc) :
    lookEnd 7 (((bindK (r2d ny ne qe)).comp (sgKA ny ⟨.inj₁ .unit, .inj₁ .unit⟩ (k2d1 ny))).plug
      (.val (Val.loc ℓ))) =
      ((bindK (r2d ny ne qe)).comp ((sgFr (.inj₁ .unit)).comp (sgKF ny (k2d1 ny)))).plug
        (freeE (.val (Val.loc ℓ))) := by
  rfl

theorem s2d_C (ny ne : UInt32) (qe : Expr) :
    lookEnd 3 (((bindK (r2d ny ne qe)).comp ((sgFr (.inj₁ .unit)).comp (sgKF ny (k2d1 ny)))).plug
      .unit) =
      ((bindK (r2d ny ne qe)).comp (sgFr (.inj₁ .unit))).plug
        (hndE (sgHV ny) (Kont.hole.plug
          (performE (.val (opPayload ny 0 ⟨.inj₂ .unit, .inj₂ .unit⟩))))) := by
  rfl

theorem s2d_D (ny ne : UInt32) (qe : Expr) (ℓ : Loc) :
    lookEnd 7 ((((bindK (r2d ny ne qe)).comp (sgFr (.inj₁ .unit))).comp
      (sgKA ny ⟨.inj₂ .unit, .inj₂ .unit⟩ .hole)).plug (.val (Val.loc ℓ))) =
      (((bindK (r2d ny ne qe)).comp (sgFr (.inj₁ .unit))).comp ((sgFr (.inj₂ .unit)).comp
        (sgKF ny .hole))).plug (freeE (.val (Val.loc ℓ))) := by
  rfl

theorem s2d_E (ny ne : UInt32) (qe : Qual) :
    lookEnd 13 ((((bindK (r2d ny ne (qualsVal [qe]).1)).comp (sgFr (.inj₁ .unit))).comp
      ((sgFr (.inj₂ .unit)).comp (sgKF ny .hole))).plug .unit) =
      (pr2dK.comp (tr2dK ne (qualsVal [qe]).1)).plug (hndE (sgHV ny) ((bindK (raiseU ne)).plug
        (performE (.val (opPayload ny 0 ⟨.inj₁ .unit, .inj₁ .unit⟩))))) := by
  rfl

theorem s2d_F (ny ne : UInt32) (qe : Qual) (ℓ : Loc) :
    lookEnd 7 (((pr2dK.comp (tr2dK ne (qualsVal [qe]).1)).comp
      (sgKA ny ⟨.inj₁ .unit, .inj₁ .unit⟩ (bindK (raiseU ne)))).plug (.val (Val.loc ℓ))) =
      ((pr2dK.comp (tr2dK ne (qualsVal [qe]).1)).comp ((sgFr (.inj₁ .unit)).comp
        (sgKF ny (bindK (raiseU ne))))).plug (freeE (.val (Val.loc ℓ))) := by
  rfl

theorem s2d_G (ny ne : UInt32) (qe : Qual) :
    lookEnd 3 (((pr2dK.comp (tr2dK ne (qualsVal [qe]).1)).comp ((sgFr (.inj₁ .unit)).comp
      (sgKF ny (bindK (raiseU ne))))).plug .unit) =
      pr2dK.plug (hndE (toResultV ne (qualsVal [qe])) (((sgFr (.inj₁ .unit)).comp
        (handleK ny (qualsVal [.aff]).1 (.lam (.inj₁ .unit)) [sgClE])).plug
          (raiseE (.val (opPayload ne 0 Val.unit))))) := by
  rfl

theorem s2d_H :
    lookEnd 2 (pr2dK.plug (.app (.val ⟨.lam (.inj₂ .unit), .lam⟩) (.val Val.unit))) =
      .pair (.inj₂ .unit) (.inj₂ .unit) := by
  rfl
theorem head_sgHop (ny : UInt32) (K : Kont) (v : Val) (hK : K.HasHnd ny = false) (μ : Heap) :
    Head (ℍ := ℍ) μ (hndE (sgHV ny) (K.plug (performE (.val (opPayload ny 0 v))))) μ
      (.app (.val ⟨sgClE, .lam⟩) (.pair (.val v) (kappaCell true ny (sgHV ny) K))) := by
  have hk : kappaAt (capTag (qualsVal [.aff]).1 (0 : UInt32).toNat) ny (sgHV ny) K =
      kappaCell true ny (sgHV ny) K := by
    simp [capTag, qualsVal, Qual.tag, kappaAt, Val.pair, Val.i32]
  have h := Head.hop (ℍ := ℍ) μ ny 0 (qualsVal [.aff]) ⟨.lam (.inj₁ .unit), .lam⟩
    ⟨clausesE [sgClE], .pair .lam .unit⟩ ⟨sgClE, .lam⟩ v K
    (clauseAt_clausesE [sgClE] 0 .lam rfl) hK
  simp only [sgHV] at hk ⊢
  rwa [hk] at h

/-- **A catch by `sumGen`'s handler, around `κ`'s cell**: in the context `Ko`, the catch of
`yield v` in `K`, the clause and the resume up to the release of `κ`'s cell (`h₁`), and on to `e'`
(`h₂`). -/
theorem cellQuiet_sgCatch (ny : UInt32) (Ko K : Kont) (v : Val) (hK : K.HasHnd ny = false)
    {e' : Expr}
    (h₁ : ∀ ℓ, Quiet (ℍ := ℍ) ((Ko.comp (sgKA ny v K)).plug (.val (Val.loc ℓ)))
      ((Ko.comp ((sgFr v.1).comp (sgKF ny K))).plug (freeE (.val (Val.loc ℓ)))))
    (h₂ : Quiet (ℍ := ℍ) ((Ko.comp ((sgFr v.1).comp (sgKF ny K))).plug .unit) e') :
    CellQuiet (ℍ := ℍ) (Ko.plug (hndE (sgHV ny) (K.plug (performE (.val (opPayload ny 0 v))))))
      e' := by
  refine ⟨Ko.comp (sgKA ny v K), ?_, fun ℓ => ⟨Ko.comp ((sgFr v.1).comp (sgKF ny K)), h₁ ℓ, h₂⟩⟩
  rw [Kont.plug_comp]
  exact Quiet.head (ℍ := ℍ) Ko (head_sgHop ny K v hK) rfl rfl

/-- **E2d's body, `s` filled by `sumGen`, runs calmly to `(tt, inr ())`**: three catches around
their cells, the second inside the first's clause, and the raise passing `sumGen`'s reinstalled
handler to `toResult`'s. -/
theorem calm_body2d (ny ne : UInt32) (qe : Qual) (hne : ne ≠ ny) :
    Calm (ℍ := ℍ) (body2dW (sumGenE ny (qualsVal [.aff]).1) ny ne (qualsVal [qe]).1)
      (.pair (.inj₂ .unit) (.inj₂ .unit)) := by
  have qA := quiet_of_look (ℍ := ℍ) 4
    (body2dW (sumGenE ny (qualsVal [.aff]).1) ny ne (qualsVal [qe]).1) rfl
  rw [s2d_A] at qA
  have c₁ := cellQuiet_sgCatch (ℍ := ℍ) ny (bindK (r2d ny ne (qualsVal [qe]).1)) (k2d1 ny)
    ⟨.inj₁ .unit, .inj₁ .unit⟩ rfl
    (fun ℓ => by
      have h := quiet_of_look (ℍ := ℍ) 7 (((bindK (r2d ny ne (qualsVal [qe]).1)).comp
        (sgKA ny ⟨.inj₁ .unit, .inj₁ .unit⟩ (k2d1 ny))).plug (.val (Val.loc ℓ))) rfl
      rwa [s2d_B] at h)
    (by
      have h := quiet_of_look (ℍ := ℍ) 3 (((bindK (r2d ny ne (qualsVal [qe]).1)).comp
        ((sgFr (.inj₁ .unit)).comp (sgKF ny (k2d1 ny)))).plug .unit) rfl
      rwa [s2d_C] at h)
  have c₂ := cellQuiet_sgCatch (ℍ := ℍ) ny ((bindK (r2d ny ne (qualsVal [qe]).1)).comp
    (sgFr (.inj₁ .unit))) .hole ⟨.inj₂ .unit, .inj₂ .unit⟩ rfl
    (fun ℓ => by
      have h := quiet_of_look (ℍ := ℍ) 7 ((((bindK (r2d ny ne (qualsVal [qe]).1)).comp
        (sgFr (.inj₁ .unit))).comp (sgKA ny ⟨.inj₂ .unit, .inj₂ .unit⟩ .hole)).plug
          (.val (Val.loc ℓ))) rfl
      rwa [s2d_D] at h)
    (by
      have h := quiet_of_look (ℍ := ℍ) 13 ((((bindK (r2d ny ne (qualsVal [qe]).1)).comp
        (sgFr (.inj₁ .unit))).comp ((sgFr (.inj₂ .unit)).comp (sgKF ny .hole))).plug .unit) rfl
      rwa [s2d_E] at h)
  have c₃ := cellQuiet_sgCatch (ℍ := ℍ) ny (pr2dK.comp (tr2dK ne (qualsVal [qe]).1)) (bindK (raiseU ne))
    ⟨.inj₁ .unit, .inj₁ .unit⟩ rfl
    (fun ℓ => by
      have h := quiet_of_look (ℍ := ℍ) 7 (((pr2dK.comp (tr2dK ne (qualsVal [qe]).1)).comp
        (sgKA ny ⟨.inj₁ .unit, .inj₁ .unit⟩ (bindK (raiseU ne)))).plug (.val (Val.loc ℓ))) rfl
      rwa [s2d_F] at h)
    (by
      have h := quiet_of_look (ℍ := ℍ) 3 (((pr2dK.comp (tr2dK ne (qualsVal [qe]).1)).comp
        ((sgFr (.inj₁ .unit)).comp (sgKF ny (bindK (raiseU ne))))).plug .unit) rfl
      rwa [s2d_G] at h)
  have hK : Kont.Catches ne ((sgFr (.inj₁ .unit)).comp
      (handleK ny (qualsVal [.aff]).1 (.lam (.inj₁ .unit)) [sgClE])) = false := by
    simp [sgFr, Kont.Catches, handleK, hndValE, Kont.comp, bindK, Ne.symm hne]
  have hB := Quiet.head (ℍ := ℍ) pr2dK (fun μ => Head.hunwind μ ne 0 (qualsVal [qe])
    ⟨.lam (.inj₁ (.var 0)), .lam⟩ ⟨clausesE [.lam (.inj₂ .unit)], .pair .lam .unit⟩
    ⟨.lam (.inj₂ .unit), .lam⟩ Val.unit _ (clauseAt_clausesE [.lam (.inj₂ .unit)] 0 .lam rfl) hK)
    rfl rfl
  have qH := quiet_of_look (ℍ := ℍ) 2 (pr2dK.plug (.app (.val ⟨.lam (.inj₂ .unit), .lam⟩)
    (.val Val.unit))) rfl
  rw [s2d_H] at qH
  exact qA.calm.trans (c₁.calm.trans (c₂.calm.trans (c₃.calm.trans (hB.trans qH).calm)))

section E2d
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

theorem prog2d_beta (ly le : (orowAlg Ξ).Lab) :
    Expr.subst 0 ⟨sumGenE ly.1 (qsOf Ξ ly.1), .lam⟩ (((𝕁).body2d ly le : Expr)) =
      body2dW (sumGenE ly.1 (qsOf Ξ ly.1)) ly.1 le.1 (qsOf Ξ le.1) := by
  simp only [A.EffectSystem.body2d, A.EffectSystem.call, A.EffectSystem.apps, List.foldl,
    A.EffectSystem.toResult, A.EffectSystem.gen1, A.EffectSystem.gen2, A.EffectSystem.tt,
    A.EffectSystem.ff]
  simp only [ourInst, List.map]
  simp [body2dW, gen1E, gen2E, sumGenE, sgClE, appE, bindE, handleK, hndValE, Kont.plug,
    Expr.shift, Expr.subst, clausesE, resumeE, qsOf, performE, raiseE, opArgE, Val.i32]

theorem fillS_body2d {σ : ℕ → Option Val} {W : Val} (hW : σ 0 = some W)
    (hWc : closedAt 0 W.1 = true) (ly le : (orowAlg Ξ).Lab) :
    fillS σ 0 ((𝕁).body2d ly le) = body2dW W.1 ly.1 le.1 (qsOf Ξ le.1) := by
  simp only [A.EffectSystem.body2d, A.EffectSystem.call, A.EffectSystem.apps, List.foldl,
    A.EffectSystem.toResult, A.EffectSystem.gen1, A.EffectSystem.gen2, A.EffectSystem.tt,
    A.EffectSystem.ff]
  simp only [ourInst, List.map]
  simp [body2dW, gen1E, gen2E, fillS, appE, bindE, handleK, hndValE, Kont.plug, hW, Expr.shift,
    clausesE, qsOf, performE, raiseE, opArgE, Val.i32, fillS_closed σ _ _ (closedAt_qualsVal _ _),
    shift_closedAt W.1 1 hWc]

/-- **E2d's body, `s` filled by a closing of `sumGen`'s type**: its two uses at the pure row and
at `exn`'s row, the generators at `yield ⊙` each. -/
theorem d_body2dW {W : Expr} (hWc : closedAt 0 W = true) {ly le : (orowAlg Ξ).Lab}
    (hWi : ∀ r : Row, Row.NU r → RowAt Ξ r → CDerivesAt Ξ LifeCtx.empty [] W
      (.comp (.arr (.thunk (.arr .unit (CTy.effOf (rowOf ly ++ r) .unit))) (CTy.effOf r boolT))))
    (hΞ : Ξ.NU) (hly : Ξ ly.1 = [(.aff, boolT, .unit)]) {qe : Qual}
    (hle : Ξ le.1 = [(qe, .unit, .zero)]) (hqe : qe ≠ .lin) (hne : ly.1 ≠ le.1) :
    CDerivesAt Ξ LifeCtx.empty [⟨.unit, false⟩] (body2dW W ly.1 le.1 (qsOf Ξ le.1))
      (.comp (.ret (.tensor boolT (.sum boolT .unit)))) := by
  have hΓ₀ : Ctx.Dead ([⟨.unit, false⟩] : Ctx VTy) := .cons .nil
  have hRe := rowAt_ofEff_lab le hle
  have hg1 : CDerivesAt Ξ LifeCtx.empty []
      (bindE (performE (opArgE ly.1 0 (.inj₁ .unit))) (performE (opArgE ly.1 0 (.inj₂ .unit))))
      (.comp (CTy.effOf (rowOf ly ++ []) .unit)) := by
    have h : CDerivesAt Ξ LifeCtx.empty []
        (bindE (performE (opArgE ly.1 0 (.inj₁ .unit))) (performE (opArgE ly.1 0 (.inj₂ .unit))))
        (.comp (CTy.effOf (Row.ofEff ly.1 [(.aff, boolT, .unit)] 0 ++ []) .unit)) :=
      .effLet (A := .unit) .nil (fun _ => fun _ h => absurd h List.not_mem_nil)
        (fun _ => fun _ h => absurd h List.not_mem_nil)
        (d_performLab ly hly rfl (.sumI₁ (.unitI .nil)))
        (d_performLab ly hly rfl (.sumI₂ (.unitI (.drop rfl .nil))))
    rwa [rowOf, hly]
  have hg2 : CDerivesAt Ξ LifeCtx.empty []
      (bindE (performE (opArgE ly.1 0 (.inj₁ .unit))) (raiseE (opArgE le.1 0 .unit)))
      (.comp (CTy.effOf (rowOf ly ++ (Row.ofEff le.1 [(qe, .unit, .zero)] 0 ++ [])) .unit)) := by
    rw [rowOf, hly]
    exact .effLet (A := .unit) .nil (fun _ => fun _ h => absurd h List.not_mem_nil)
      (fun _ => fun _ h => absurd h List.not_mem_nil)
      (.effSub (rowLe_append_nil _ _) (d_performLab ly hly rfl (.sumI₁ (.unitI .nil))))
      (.effSub (rowLe_ofEff_cons _ (names_ofEff (Ne.symm hne)))
        (d_raiseLab (.drop rfl .nil) le hle hqe .unit))
  refine .bind (deadSplit hΓ₀) (d_appClosed hΓ₀ hWc (hWi [] row_nu_nil (rowAt_nil Ξ))
    (d_cbDead hΓ₀ hg1)) ?_
  refine .bind (A := .sum boolT .unit) (.right (deadSplit hΓ₀)) ?_ ?_
  · refine d_handleL le hle (S := []) (rowAt_nil Ξ) (by simp) isVal_toResultH
      (d_toResultH (kill_dead _) [] boolT hqe) ?_
    exact d_appClosed (.cons hΓ₀) hWc (hWi _ (rowNU_of_rowAt hΞ hRe) hRe) (d_cbDead (.cons hΓ₀) hg2)
  exact .ret (.tensorI (.right (.left (.dead .nil))) (.var (.there (.here (.cons .nil))))
    (.var (.here (.cons (.cons .nil)))))

/-- **E2d's body is typed at `J₁`**, `s` at `sumGen`'s polymorphic type. -/
theorem der_body2d_J₁ (hΞ : Ξ.NU) {ly le : (orowAlg Ξ).Lab} (hly : Ξ ly.1 = [(.aff, boolT, .unit)])
    {qe : Qual} (hle : Ξ le.1 = [(qe, .unit, .zero)]) (hqe : qe ≠ .lin) (hne : ly.1 ≠ le.1) :
    (𝕁).der [polyTy (sgC (rowOf ly))] ((𝕁).body2d ly le) ((𝕁).F (𝕁).EA.unit (𝕁).ty2d) := by
  refine ⟨tiedAt_unit J₁ _, .inl ⟨[], by simp, slots_polyTy (sgC_rFree _) trivial,
    OVTy.rFree_ofV (.tensor boolT (.sum boolT .unit)), fun η _ _ σ hσ => ?_⟩⟩
  obtain ⟨W, hW, -, hWc, hWty⟩ := closingAt_one (polyTy_isPoly _) hσ
  show CDerivesAt Ξ LifeCtx.empty (octxStrip η (liveCtx [polyTy (sgC (rowOf ly))]))
    (fillS σ 0 ((𝕁).body2d ly le)) (.comp (.ret (.tensor boolT (.sum boolT .unit))))
  rw [fillS_body2d hW hWc, octxStrip_live_cons_poly η (polyTy_isPoly _) []]
  refine d_body2dW hWc (fun r hr hrt => ?_) hΞ hly hle hqe hne
  have := hWty _ ⟨r, ⟨hr, fun _ _ => trivial⟩, hrt, rfl⟩
  rwa [sgC_den] at this

/-- **E2d's run**: it answers `(tt, inr ())`, showing nothing. -/
theorem runsTo_prog2d {ly le : (orowAlg Ξ).Lab} (hly : Ξ ly.1 = [(.aff, boolT, .unit)]) {qe : Qual}
    (hle : Ξ le.1 = [(qe, .unit, .zero)]) (hne : le.1 ≠ ly.1) :
    (𝕁).RunsTo (𝕁).R₀ ((𝕁).prog2d ly le) ((𝕁).pair (𝕁).tt ((𝕁).inr (𝕁).unitV)) [] := by
  have h₀ := quiet_beta (ℍ := ℍ) .hole ((𝕁).body2d ly le) ⟨sumGenE ly.1 (qsOf Ξ ly.1), .lam⟩
  rw [prog2d_beta] at h₀
  have e₁ : qsOf Ξ ly.1 = (qualsVal [.aff]).1 := qsOf_eq hly
  have e₂ : qsOf Ξ le.1 = (qualsVal [qe]).1 := qsOf_eq hle
  have hc := calm_body2d (ℍ := ℍ) ly.1 le.1 qe hne
  rw [← e₁, ← e₂] at hc
  have h := (show Quiet (ℍ := ℍ) ((𝕁).prog2d ly le) _ from h₀).calm.trans hc
  exact runsTo_of_calm (𝕁).R₀ (v := ⟨_, .pair (.inj₂ .unit) (.inj₂ .unit)⟩) h

/-- **E2, its fourth program (E2d) at `J₁`**: `sumGen` is typed once and serves a generator at
every `yield ⊙ ε`; the body is typed and runs to `(tt, inr ())`.  At a context with no `unr`
operation. -/
theorem e2d_J₁ (hΞ : Ξ.NU) (hX : NoUnr Ξ) {ly le : (orowAlg Ξ).Lab}
    (hly : Ξ ly.1 = [(.aff, boolT, .unit)]) {qe : Qual} (hle : Ξ le.1 = [(qe, .unit, .zero)])
    (hqe : qe ≠ .lin) (hne : ly.1 ≠ le.1) :
    ∃ As, (𝕁).derV [] ((𝕁).sumGen ly) As ∧
      (𝕁).PolyUseOpen [As] ly (fun g => (𝕁).call ((𝕁).var 0) g) (𝕁).UnitT (𝕁).bool ∧
      (𝕁).der [As] ((𝕁).body2d ly le) ((𝕁).F (𝕁).EA.unit (𝕁).ty2d) ∧
      (𝕁).RunsTo (𝕁).R₀ ((𝕁).prog2d ly le) ((𝕁).pair (𝕁).tt ((𝕁).inr (𝕁).unitV)) [] :=
  ⟨_, derV_sumGen_J₁ hly hX, polyUseOpen_sumGen_J₁ hΞ ly, der_body2d_J₁ hΞ hly hle hqe hne,
    runsTo_prog2d hly hle (Ne.symm hne)⟩

/-- **E2's fourth conjunct at `J₁`**, at every label list `HigherOrderPoly` quantifies over, at an
effect context with no resuming `unr` operation and no `unr` operation at all. -/
theorem higherOrderPoly_e2d_J₁ (hΞ : Ξ.NU) (hX : NoUnr Ξ) (ls : List (orowAlg Ξ).Lab)
    (hls : (𝕁).LabelsAt [(𝕁).sigExn, (𝕁).sigWait, (𝕁).sigYield, (𝕁).sigLog] ls)
    (le lw ly llog : (orowAlg Ξ).Lab) (hlsEq : ls = [le, lw, ly, llog]) :
    ∃ As, (𝕁).derV [] ((𝕁).sumGen ly) As ∧
      (𝕁).PolyUseOpen [As] ly (fun g => (𝕁).call ((𝕁).var 0) g) (𝕁).UnitT (𝕁).bool ∧
      (𝕁).der [As] ((𝕁).body2d ly le) ((𝕁).F (𝕁).EA.unit (𝕁).ty2d) ∧
      (𝕁).RunsTo (𝕁).R₀ ((𝕁).prog2d ly le) ((𝕁).pair (𝕁).tt ((𝕁).inr (𝕁).unitV)) [] := by
  subst hlsEq
  have h₀ := hls.2.2 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
  have h₂ := hls.2.2 2 (by show 2 < 4; decide) (by show 2 < 4; decide)
  obtain ⟨qe, hle, hqe⟩ := (sig_exn_iff le).mp h₀
  have hly := (sig_yield_iff hΞ ly).mp h₂
  have hne : ly.1 ≠ le.1 := fun h => by
    rw [h, hle] at hly
    simp at hly
  exact e2d_J₁ hΞ hX hly hle hqe hne

end E2d

end Targets.Inst

end
