import Core.Family
import Core.RecordPrograms

/-!
# Core — programs over place families  `[spec §5]`

Closed programs typed at `1`, each run by `adequacyC` and by the interpreter; each `…Obs`
variant returns what the place-record holds at the end.

| program | shows |
|---|---|
| `swapBoth A` | `Mut 'c` at `s.a` and at `s.b` held together: `mem::swap(&mut s.a, &mut s.b)`, at any payload that outlives every lifetime; run at `1 ⊕ 1` (`swapBothB`) and at the common list (`swapBothL`) |
| `readFamily` | the `Imm` family: copied, one leaf read by one function, the whole family by another, all at `'c` |
| `splitFour` | a 4-leaf family from two nested `withborF2`s and `⊑Mut`, split into halves at one lifetime (`split_at_mut`, static `n`) |
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Programs (alloc' free' app2 unitNoLeak entailsLt_top interp_meet_left)

/-! ### Two mutable borrows at one lifetime, used together

    let (s, u) = withborF2 (alloc v₁, alloc v₂) (Λ. λm.
                   let (ma, mb) = m;
                   let (ma′, u₁) = withswap ma (λva.
                                     let (mb′, vb) = withswap mb (λvb. (va, vb));
                                     forget mb′; (vb, ()));
                   u₁; forget ma′; ());
    u; let (ra, rb) = s; drop (free ra); drop (free rb) -/

/-- `λvb. (va, vb)`, `va` at index 1. -/
def swapIn : Expr := .val (.lam (.pair (.var 1) (.var 0)))

/-- `λva. let (mb′, vb) = withswap mb swapIn; forget mb′; (vb, ())`, `mb` at index 1. -/
def swapOut : Expr :=
  .val (.lam (.letpair (app2 withswap (.var 1) swapIn)
    (.seq (.app forget (.var 1)) (.pair (.var 0) unit'))))

/-- The swap on `ma` (index 1) and `mb` (index 0), ending in `forget ma′; ()`. -/
def swapBody : Expr :=
  .letpair (app2 withswap (.var 1) swapOut) (.seq (.var 0) (.seq (.app forget (.var 1)) unit'))

def swapCb : Expr := .val (.lam (.val (.lam (.letpair (.var 0) swapBody))))

/-- The program at payload values `e₁`, `e₂` and a consumer `dropE : A ⊸ 1`. -/
def swapBoth (e₁ e₂ dropE : Expr) : Expr :=
  .letpair (app2 withborF2 (.pair (.app alloc' e₁) (.app alloc' e₂)) swapCb)
    (.seq (.var 0) (.letpair (.var 1)
      (.seq (.app dropE (.app free' (.var 1))) (.app dropE (.app free' (.var 0))))))

/-- The same run, returning the contents, each through `outE`. -/
def swapBothObs (e₁ e₂ outE : Expr) : Expr :=
  .letpair (app2 withborF2 (.pair (.app alloc' e₁) (.app alloc' e₂)) swapCb)
    (.seq (.var 0) (.letpair (.var 1)
      (.pair (.app outE (.app free' (.var 1))) (.app outE (.app free' (.var 0))))))

section
variable {A : VTy}

theorem d_swapIn {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ (⟨A, true⟩ :: Γ) swapIn (.val (.lolli A (.tensor A A))) :=
  .lamV (pairW (.var (by csolo)) (.var (by csolo)))

theorem d_swapOut {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} (hΓ : Ctx.Dead Γ) :
    CDerives Δ (⟨.mut a A, true⟩ :: Γ) swapOut (.val (.lolli A (.tensor A .unit))) :=
  .lamV <|
    letW (A := .mut a A) (B := A)
      (appW (d_swapIn (by cdead)) (appW (.var (by csolo)) (.withswap (by cdead)))) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead))) (pairW (.var (by csolo)) (.unitI (by cdead)))

theorem d_swapCb (hA : ∀ z, ¬ VFree z A) :
    CDerives LifeCtx.empty [] swapCb (.val (cbTy2 mutM 0 LifeCtx.empty.meetOfDom A A .unit)) :=
  callbackW ok_empty rfl .nil <|
    letW (A := .mut (.var 0) A) (B := .mut (.var 0) A) (.var (by csolo)) <|
    letW (A := .mut (.var 0) A) (B := .unit)
      (appW (d_swapOut (by cdead)) (appW (.var (by csolo)) (.withswap (by cdead)))) <|
    seqW (.var (by csolo)) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead)))
      (.boxI (.unitI (by cdead)) ⟨LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩)

/-- `FamSide` at `Δ = ∅`, binders `'c = 0`, `'a = 1`, `'b = 2`, a closed payload. -/
theorem famSide0 (M : Lifetime.Life → VTy → VTy) (T : VTy) (hA : ∀ z, ¬ VFree z A)
    (hT : ∀ z, ¬ VFree z T)
    (hM : ∀ z a S, VFree z (M a S) ↔ (a.mentions z = true ∨ VFree z S))
    (hinst : VTy.instLife 0 (.var 2) (.lolli (famTy2 M (.var 0) A A) (.box (.var 0) T))
      = .lolli (famTy2 M (.var 2) A A) (.box (.var 2) T)) :
    FamSide M LifeCtx.empty 0 1 2 A A T := by
  have hcb : ∀ z, z ≠ 0 → ¬ VFree z (cbTy2 M 0 LifeCtx.empty.meetOfDom A A T) := by
    intro z hz h
    simp only [cbTy2, famTy2, VFree, CFree, hM, Lifetime.Life.mentions] at h
    rcases h with h | ⟨-, (((h | h) | (h | h)) | (h | h))⟩
    · simp [LifeCtx.meetOfDom, LifeCtx.empty, Lifetime.meetOfDomL, Lifetime.Life.mentions] at h
    · simp at h; exact hz h
    · exact hA z h
    · simp at h; exact hz h
    · exact hA z h
    · simp at h; exact hz h
    · exact hT z h
  exact ⟨ok_empty, rfl, rfl, by decide, hA 1, hA 1, hT 1, hA 2, hA 2, hT 2, hcb 1 (by decide),
    hcb 2 (by decide), hinst⟩

/-- `withborF2` at `Mut`, `Δ = ∅`, payload `A`, result `1`. -/
theorem d_withborM2A (hA : ∀ z, ¬ VFree z A) (hAo : ∀ Δ a, VOutlives Δ a A)
    (hinst : VTy.instLife 0 (.var 2) (.lolli (famTy2 mutM (.var 0) A A) (.box (.var 0) .unit))
      = .lolli (famTy2 mutM (.var 2) A A) (.box (.var 2) .unit))
    {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ withborF2
      (.val (withborF2Ty mutM 0 LifeCtx.empty.meetOfDom A A .unit)) :=
  withborM2_wf (famSide0 mutM .unit hA (fun _ h => h) (fun _ _ _ => Iff.rfl) hinst)
    ⟨.top, LifeCtx.defines_of_wf rfl, hAo _ _⟩ (hAo _ _) .unit hΓ

theorem d_swapBoth {e₁ e₂ dropE : Expr} (hA : ∀ z, ¬ VFree z A) (hAo : ∀ Δ a, VOutlives Δ a A)
    (hinst : VTy.instLife 0 (.var 2) (.lolli (famTy2 mutM (.var 0) A A) (.box (.var 0) .unit))
      = .lolli (famTy2 mutM (.var 2) A A) (.box (.var 2) .unit))
    (h₁ : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives LifeCtx.empty Γ e₁ (.val A))
    (h₂ : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives LifeCtx.empty Γ e₂ (.val A))
    (hd : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives LifeCtx.empty Γ dropE (.val (.lolli A .unit))) :
    CDerives LifeCtx.empty [] (swapBoth e₁ e₂ dropE) (.val .unit) := by
  refine letW (A := refs2 A A) (B := .unit)
    (appW (d_swapCb hA)
      (appW (pairW (appW (h₁ (by cdead)) (.alloc (by cdead)))
          (appW (h₂ (by cdead)) (.alloc (by cdead))))
        (d_withborM2A hA hAo hinst (by cdead)))) ?_
  refine seqW (.var (by csolo)) ?_
  refine letW (A := .ref A) (B := .ref A) (.var (by csolo)) ?_
  have hr : Ctx.Dead (part (.var 1) 0 (part (.var 0) 0
      [⟨.unit, true⟩, ⟨refs2 A A, true⟩]).2).2 := by cdead
  exact .seqV (.right (.left (deadSplit hr)))
    (.lolliE (.dead (.left (deadSplit hr)))
      (.lolliE (.dead (.left (deadSplit hr))) (.var (.there (.here hr.toP))) (.free (.cons (.cons hr.toP))))
      (hd (.cons (.cons hr))))
    (.lolliE (.left (.dead (deadSplit hr)))
      (.lolliE (.left (.dead (deadSplit hr))) (.var (.here (.cons hr.toP))) (.free (.cons (.cons hr.toP))))
      (hd (.cons (.cons hr))))

end

/-- `λb. drop b`. -/
def dropBF : Expr := .val (.lam (dropB (.var 0)))

theorem d_dropBF {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ dropBF (.val (.lolli BB .unit)) :=
  .lamV (d_dropB (.var (by csolo)) (by cdead))

/-- At `1 ⊕ 1`: `(inj₁ (), inj₂ ())` swapped. -/
def swapBothB : Expr := swapBoth (.inj₁ unit') (.inj₂ unit') dropBF

theorem d_swapBothB : CDerives LifeCtx.empty [] swapBothB (.val .unit) :=
  d_swapBoth (A := BB) (fun _ h => by simp [VFree] at h) (fun _ _ => outlives_of_dataB rfl) rfl
    (fun hΓ => .sumI₁ (.unitI hΓ)) (fun hΓ => .sumI₂ (.unitI hΓ)) d_dropBF

theorem swapBothB_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem swapBothB Adequacy.emptyMem (.val .unit) :=
  adequacyC (.ret d_swapBothB)

theorem swapBothB_eval : unitNoLeak (eval swapBothB) = true := by decide

/-- `s.a` and `s.b` swapped: `(inj₂ (), inj₁ ())` from `(inj₁ (), inj₂ ())`. -/
theorem swapBothBObs_eval :
    (match eval (swapBothObs (.inj₁ unit') (.inj₂ unit') (.val (.lam (.var 0)))) with
      | .value ⟨.pair (.inj₂ .unit) (.inj₁ .unit), _⟩ false => true
      | _ => false) = true := by decide

/-- At the common list: `[1, 2]` and `[3]` swapped. -/
def swapBothL : Expr := swapBoth (buildList [1, 2]) (buildList [3]) freeCE

theorem d_swapBothL : CDerives LifeCtx.empty [] swapBothL (.val .unit) :=
  d_swapBoth (A := clistL) (fun _ h => by simp [VFree, clistL, FShape.ty, natN, natBody] at h)
    clistL_outlives rfl (fun hΓ => d_buildList hΓ _) (fun hΓ => d_buildList hΓ _) d_freeC

theorem swapBothL_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem swapBothL Adequacy.emptyMem (.val .unit) :=
  adequacyC (.ret d_swapBothL)

set_option maxRecDepth 100000 in
theorem swapBothL_eval : unitNoLeak (eval swapBothL) = true := by decide

/-- Both lists' numerals, when the run ends with no cell left. -/
def purePairNoLeak : Outcome → Option (List Nat × List Nat)
  | .value v false =>
      match v.1 with
      | .pair p q => do
          let l ← pureOf p
          let r ← pureOf q
          pure (l, r)
      | _ => none
  | _ => none

set_option maxRecDepth 100000 in
/-- The lists swapped: `([3], [1, 2])`. -/
theorem swapBothLObs_eval :
    purePairNoLeak (eval (swapBothObs (buildList [1, 2]) (buildList [3]) toPureCE))
      = some ([3], [1, 2]) := by decide

/-! ### The `Imm` family

    readOne  : ∀'d ⊏ ⊤. Imm 'd B ⊸ B                          ≜ Λ. λi. withload i (Λ. λv. v)
    readBoth : ∀'d ⊏ ⊤. Imm 'd B ⊗ Imm 'd B ⊸ B ⊗ B          ≜ Λ. λp. let (i, j) = p; (readOne () i, readOne () j)

    let (s, w) = withborF2 (alloc (inj₁ ()), alloc (inj₂ ())) (Λ. λi.
                   let (ia, ib) = i;
                   let (ia₁, ia₂) = copy ia;
                   let v = readOne () ia₂;           -- sub-family s.a, at 'c
                   let w = readBoth () (ia₁, ib);     -- whole family, at 'c
                   (v, w));
    drop w; let (ra, rb) = s; drop (free ra); drop (free rb) -/

/-- `Λ. λi. withload i (Λ. λv. v)`. -/
def readOne : Expr := lam2 (app2 withload (.var 0) (lam2 (.var 0)))

/-- `Λ. λp. let (i, j) = p; (readOne () i, readOne () j)`. -/
def readBoth : Expr :=
  lam2 (.letpair (.var 0) (.pair (.app (.app readOne unit') (.var 1))
    (.app (.app readOne unit') (.var 0))))

/-- `Δ ⊨ @b` mentions no variable `Δ` does not bind, at a fresh `'d ⊏ ⊤`. -/
theorem allI_top {Δ : LifeCtx} {Γ : Ctx VTy} {S : VTy} {M : Expr} {d : LifeVar} {C : CTy}
    (hΔ : Δ.Ok) (hd : Δ.find? d = none) (hΓ : Ctx.Dead Γ)
    (h : CDerives (Δ.extend d .top) (⟨S, false⟩ :: Γ) M (.comp C)) :
    CDerives Δ Γ (.val (.lam M)) (.comp (.all d .top C)) :=
  .allI rfl (fun _ _ h => hΔ.bound_mentions_false hd h) (dead_noLive hΓ) h

theorem d_readOne {Δ : LifeCtx} {Γ : Ctx VTy} (hΔ : Δ.Ok) (hΓ : Ctx.Dead Γ) (d e : LifeVar)
    (hd : Δ.find? d = none) (he : (Δ.extend d .top).find? e = none) :
    CDerives Δ Γ readOne (.val (.all d .top (.lolli (.imm (.var d) BB) BB))) := by
  have hΔ' : (Δ.extend d .top).Ok := hΔ.extend hd rfl
  refine .thunkV rfl (allI_top (S := .unit) hΔ hd hΓ (.ret (.lamV ?_)))
  exact appW
    (callbackW hΔ' he (by cdead)
      (.boxI (.var (by csolo))
        (CtxOutlives.solo (LifeCtx.defines_of_wf (wf_var_self _ _ _)) (outlives_of_dataB rfl)
          (by cdead))))
    (appW (.var (by csolo))
      (.withload (a := .var d) (A := BB) (B := BB) e (by cdead) he (by simp [VFree])
        (by simp [VFree])))

/-- `readOne ()` at `'x`, in a context binding `'x`. -/
theorem d_readOneAt {Δ : LifeCtx} {Γ : Ctx VTy} (hΔ : Δ.Ok) (hΓ : Ctx.Dead Γ) (x d e : LifeVar)
    {u : Lifetime.Life} (hx : Δ.find? x = some u) (hd : Δ.find? d = none)
    (he : (Δ.extend d .top).find? e = none)
    (hinst : VTy.instLife d (.var x) (.lolli (.imm (.var d) BB) BB) = .lolli (.imm (.var x) BB) BB) :
    CDerives Δ Γ (.app readOne unit') (.val (.lolli (.imm (.var x) BB) BB)) := by
  have h := CDerives.allEV (a := .var x) (d_readOne hΔ hΓ d e hd he) (entailsLt_top hx)
  rwa [hinst] at h

theorem d_readBoth {Δ : LifeCtx} {Γ : Ctx VTy} (hΔ : Δ.Ok) (hΓ : Ctx.Dead Γ) (d d' e : LifeVar)
    (hd : Δ.find? d = none) (hd' : (Δ.extend d .top).find? d' = none)
    (he : ((Δ.extend d .top).extend d' .top).find? e = none)
    (hinst : VTy.instLife d' (.var d) (.lolli (.imm (.var d') BB) BB) = .lolli (.imm (.var d) BB) BB) :
    CDerives Δ Γ readBoth (.val (.all d .top (.lolli (famTy2 immM (.var d) BB BB) (.tensor BB BB)))) := by
  have hΔ' : (Δ.extend d .top).Ok := hΔ.extend hd rfl
  refine .thunkV rfl (allI_top (S := .unit) hΔ hd hΓ (.ret (.lamV ?_)))
  exact letW (A := .imm (.var d) BB) (B := .imm (.var d) BB) (.var (by csolo)) <|
    pairW
      (appW (.var (by csolo))
        (d_readOneAt hΔ' (by cdead) d d' e (u := .top) (by simp [LifeCtx.find?_extend]) hd' he
          hinst))
      (appW (.var (by csolo))
        (d_readOneAt hΔ' (by cdead) d d' e (u := .top) (by simp [LifeCtx.find?_extend]) hd' he
          hinst))

/-- The callback body after `copy`: `ia₂` at 0, `ia₁` at 1, `ib` at 2. -/
def readRest : Expr :=
  elet (.app (.app readOne unit') (.var 0))
    (elet (.app (.app readBoth unit') (.pair (.var 2) (.var 3))) (.pair (.var 1) (.var 0)))

def readCb : Expr := lam2 (.letpair (.var 0) (.letpair (.app copy (.var 1)) readRest))

/-- `B ⊗ (B ⊗ B)`. -/
abbrev B3 : VTy := .tensor BB (.tensor BB BB)

/-- `let (x, yz) = w; drop x; let (y, z) = yz; drop y; drop z`, with `w` at index `i`. -/
def dropB3 (i : Nat) : Expr :=
  .letpair (.var i) (.seq (dropB (.var 1)) (.letpair (.var 0) (.seq (dropB (.var 1)) (dropB (.var 0)))))

def readFamily : Expr :=
  .letpair (app2 withborF2 (.pair (.app alloc' (.inj₁ unit')) (.app alloc' (.inj₂ unit'))) readCb)
    (.seq (dropB3 0) (.letpair (.var 1)
      (.seq (dropB (.app free' (.var 1))) (dropB (.app free' (.var 0))))))

def readFamilyObs : Expr :=
  .letpair (app2 withborF2 (.pair (.app alloc' (.inj₁ unit')) (.app alloc' (.inj₂ unit'))) readCb)
    (.seq (.letpair (.var 1) (.seq (dropB (.app free' (.var 1))) (dropB (.app free' (.var 0)))))
      (.var 0))

theorem d_withborI2B {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ withborF2
      (.val (withborF2Ty immM 0 LifeCtx.empty.meetOfDom BB BB B3)) :=
  withborI2_wf (famSide0 (A := BB) immM B3 (fun _ h => by simp [VFree] at h)
      (fun _ h => by simp [VFree] at h) (fun _ _ _ => Iff.rfl) rfl)
    (fun _ h => by simp [VFree] at h) (fun _ h => by simp [VFree] at h)
    (outlives_of_dataB rfl) (outlives_of_dataB rfl) hΓ

theorem d_readCb :
    CDerives LifeCtx.empty [] readCb (.val (cbTy2 immM 0 LifeCtx.empty.meetOfDom BB BB B3)) :=
  callbackW ok_empty rfl .nil <|
    letW (A := .imm (.var 0) BB) (B := .imm (.var 0) BB) (.var (by csolo)) <|
    letW (A := .imm (.var 0) BB) (B := .imm (.var 0) BB)
      (appW (.var (by csolo)) (.copy (by cdead))) <|
    eletW (appW (.var (by csolo)) (d_readOneAt d1_ok (by cdead) 0 5 6 rfl rfl rfl rfl)) <|
    eletW
      (appW (pairW (.var (by csolo)) (.var (by csolo)))
        (.allEV (x := 5) (b := .top) (A := .lolli (famTy2 immM (.var 5) BB BB) (.tensor BB BB))
          (a := .var 0) (d_readBoth d1_ok (by cdead) 5 6 7 rfl rfl rfl rfl) (entailsLt_top rfl))) <|
    .boxI (pairW (.var (by csolo)) (.var (by csolo)))
      (outlives_two (LifeCtx.defines_of_wf rfl) (outlives_of_dataB rfl) (outlives_of_dataB rfl)
        (by cdead))

theorem d_dropB3 {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ (⟨B3, true⟩ :: Γ) (dropB3 0) (.val .unit) :=
  letW (A := BB) (B := .tensor BB BB) (.var (by csolo)) <|
  seqW (d_dropB (.var (by csolo)) (by cdead)) <|
  letW (A := BB) (B := BB) (.var (by csolo)) <|
  seqW (d_dropB (.var (by csolo)) (by cdead)) (d_dropB (.var (by csolo)) (by cdead))

theorem d_readFamily : CDerives LifeCtx.empty [] readFamily (.val .unit) :=
  letW (A := refs2 BB BB) (B := B3)
    (appW d_readCb
      (appW (pairW (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead)))
          (appW (.sumI₂ (.unitI (by cdead))) (.alloc (by cdead))))
        (d_withborI2B (by cdead)))) <|
  seqW (d_dropB3 (by cdead)) <|
  letW (A := .ref BB) (B := .ref BB) (.var (by csolo)) <|
  seqW (d_dropB (appW (.var (by csolo)) (.free (by cdead))) (by cdead))
    (d_dropB (appW (.var (by csolo)) (.free (by cdead))) (by cdead))

theorem readFamily_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem readFamily Adequacy.emptyMem (.val .unit) :=
  adequacyC (.ret d_readFamily)

theorem readFamily_eval : unitNoLeak (eval readFamily) = true := by decide

/-- `s.a` read alone, then `(s.a, s.b)` read as a family: `(inj₁ (), (inj₁ (), inj₂ ()))`. -/
theorem readFamilyObs_eval :
    (match eval readFamilyObs with
      | .value ⟨.pair (.inj₁ .unit) (.pair (.inj₁ .unit) (.inj₂ .unit)), _⟩ false => true
      | _ => false) = true := by decide

/-! ### Nesting: `split_at_mut` at a static length

A slice of four is the place-record `((r₀, r₁), (r₂, r₃))`.  Its family at one lifetime is two
`withborF2`s nested: the outer borrows `(r₀, r₁)` at `'c`, the inner borrows `(r₂, r₃)` at
`'e ⊏ 'c`, and `⊑Mut` shortens `r₀`'s and `r₁`'s borrows to `'e`.  `split_at_mut(2)` is `⊗E` on
the family:

    swapHalves : ∀'d ⊏ ⊤. (Mut 'd B ⊗ Mut 'd B) ⊗ (Mut 'd B ⊗ Mut 'd B) ⊸ 1
    swapHalves ≜ Λ. λf. let (lo, hi) = f;
                        let (l₀, l₁) = swapFn () lo; let (h₀, h₁) = swapFn () hi;
                        forget l₀; forget l₁; forget h₀; forget h₁ -/

/-- `λva. let (mb′, vb) = withswap mb swapIn; (vb, mb′)`, `mb` at index 1. -/
def swapOutK : Expr :=
  .val (.lam (.letpair (app2 withswap (.var 1) swapIn) (.pair (.var 0) (.var 1))))

/-- `Λ. λm. let (ma, mb) = m; withswap ma swapOutK`. -/
def swapFn : Expr := lam2 (.letpair (.var 0) (app2 withswap (.var 1) swapOutK))

/-- `Mut 'd B ⊗ Mut 'd B ⊸ Mut 'd B ⊗ Mut 'd B`. -/
abbrev famEndo (d : LifeVar) : VTy :=
  .lolli (famTy2 mutM (.var d) BB BB) (famTy2 mutM (.var d) BB BB)

theorem d_swapOutK {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} (hΓ : Ctx.Dead Γ) :
    CDerives Δ (⟨.mut a BB, true⟩ :: Γ) swapOutK (.val (.lolli BB (.tensor BB (.mut a BB)))) :=
  .lamV <|
    letW (A := .mut a BB) (B := BB)
      (appW (d_swapIn (by cdead)) (appW (.var (by csolo)) (.withswap (by cdead)))) <|
    pairW (.var (by csolo)) (.var (by csolo))

theorem d_swapFn {Δ : LifeCtx} {Γ : Ctx VTy} (hΔ : Δ.Ok) (hΓ : Ctx.Dead Γ) (d : LifeVar)
    (hd : Δ.find? d = none) : CDerives Δ Γ swapFn (.val (.all d .top (famEndo d))) :=
  .thunkV rfl <| allI_top (S := .unit) hΔ hd hΓ <| .ret <| .lamV <|
    letW (A := .mut (.var d) BB) (B := .mut (.var d) BB) (.var (by csolo)) <|
    appW (d_swapOutK (by cdead)) (appW (.var (by csolo)) (.withswap (by cdead)))

theorem d_swapFnAtVar {Δ : LifeCtx} {Γ : Ctx VTy} (hΔ : Δ.Ok) (hΓ : Ctx.Dead Γ) (x d : LifeVar)
    {u : Lifetime.Life} (hx : Δ.find? x = some u) (hd : Δ.find? d = none)
    (hinst : VTy.instLife d (.var x) (famEndo d) = famEndo x) :
    CDerives Δ Γ (.app swapFn unit') (.val (famEndo x)) := by
  have h := CDerives.allEV (a := .var x) (d_swapFn hΔ hΓ d hd) (entailsLt_top hx)
  rwa [hinst] at h

/-- `(Mut @a B ⊗ Mut @a B) ⊗ (Mut @a B ⊗ Mut @a B)`. -/
abbrev fam4 (a : Lifetime.Life) : VTy := .tensor (famTy2 mutM a BB BB) (famTy2 mutM a BB BB)

def swapHalves : Expr :=
  lam2 (.letpair (.var 0)
    (.letpair (.app (.app swapFn unit') (.var 1))
      (.letpair (.app (.app swapFn unit') (.var 2))
        (.seq (.app forget (.var 0)) (.seq (.app forget (.var 1))
          (.seq (.app forget (.var 2)) (.app forget (.var 3))))))))

theorem d_swapHalves {Δ : LifeCtx} {Γ : Ctx VTy} (hΔ : Δ.Ok) (hΓ : Ctx.Dead Γ) (d d' : LifeVar)
    (hd : Δ.find? d = none) (hd' : (Δ.extend d .top).find? d' = none)
    (hinst : VTy.instLife d' (.var d) (famEndo d') = famEndo d) :
    CDerives Δ Γ swapHalves (.val (.all d .top (.lolli (fam4 (.var d)) .unit))) := by
  have hΔ' : (Δ.extend d .top).Ok := hΔ.extend hd rfl
  have hx : (Δ.extend d .top).find? d = some .top := by simp [LifeCtx.find?_extend]
  exact .thunkV rfl <| allI_top (S := .unit) hΔ hd hΓ <| .ret <| .lamV <|
    letW (A := famTy2 mutM (.var d) BB BB) (B := famTy2 mutM (.var d) BB BB) (.var (by csolo)) <|
    letW (A := .mut (.var d) BB) (B := .mut (.var d) BB)
      (appW (.var (by csolo)) (d_swapFnAtVar hΔ' (by cdead) d d' hx hd' hinst)) <|
    letW (A := .mut (.var d) BB) (B := .mut (.var d) BB)
      (appW (.var (by csolo)) (d_swapFnAtVar hΔ' (by cdead) d d' hx hd' hinst)) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead))) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead))) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead)))
      (appW (.var (by csolo)) (.forgetMut (by cdead)))

/-- `'y ⊑ 'x` when `'y` is bound below `'x ⊓ u`. -/
theorem entailsLe_of_meet {Δ : LifeCtx} {x y : LifeVar} {u : Lifetime.Life}
    (h : Δ.find? y = some (.meet (.var x) u)) : Δ.EntailsLe (.var y) (.var x) := by
  intro δ hδ
  obtain ⟨m, n, hm, hn, hlt⟩ := hδ y _ h
  obtain ⟨p, hp, hpn⟩ := interp_meet_left hn
  exact ⟨m, p, hm, hp, Nat.le_of_lt (Nat.lt_of_le_of_lt hpn hlt)⟩

def innerCb : Expr :=
  lam2 (.letpair (.var 2)
    (.seq (.app (.app swapHalves unit') (.pair (.pair (.var 1) (.var 0)) (.var 2))) unit'))

def outerCb : Expr :=
  lam2 (.letpair (app2 withborF2 (.var 2) innerCb) (.pair (.var 1) (.var 0)))

/-- `(alloc v₁, alloc v₂)`. -/
def allocPair (e₁ e₂ : Expr) : Expr := .pair (.app alloc' e₁) (.app alloc' e₂)

def slice4 : Expr := .pair (allocPair (.inj₁ unit') (.inj₂ unit')) (allocPair (.inj₁ unit') (.inj₂ unit'))

/-- `let (ra, rb) = r; drop (free ra); drop (free rb)`, with `r` at index `i`. -/
def freePair (i : Nat) : Expr :=
  .letpair (.var i) (.seq (dropB (.app free' (.var 1))) (dropB (.app free' (.var 0))))

/-- `let (ra, rb) = r; (free ra, free rb)`. -/
def readPair (i : Nat) : Expr :=
  .letpair (.var i) (.pair (.app free' (.var 1)) (.app free' (.var 0)))

def splitFour : Expr :=
  .letpair slice4
    (.letpair (app2 withborF2 (.var 1) outerCb)
      (.letpair (.var 0) (.seq (.var 0) (.seq (freePair 3) (freePair 1)))))

def splitFourObs : Expr :=
  .letpair slice4
    (.letpair (app2 withborF2 (.var 1) outerCb)
      (.letpair (.var 0) (.seq (.var 0) (.pair (readPair 3) (readPair 1)))))

theorem d_innerCb {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {S₁ : VTy} :
    CDerives D1 (⟨famTy2 mutM (.var 0) BB BB, true⟩ :: ⟨S₁, false⟩ :: Γ) innerCb
      (.val (cbTy2 mutM 3 D1.meetOfDom BB BB .unit)) := by
  refine .thunkV rfl (.allI (S := .unit) rfl
    (fun _ _ h => d1_ok.bound_mentions_false rfl h) ?_ (.ret (.lamV ?_)))
  · intro t ht hl
    simp only [List.mem_cons] at ht
    rcases ht with rfl | rfl | ht
    · simp [famTy2, VFree, Lifetime.Life.mentions]
    · simp at hl
    · exact dead_noLive hΓ (P := fun t => ¬ VFree 3 t.ty) t ht hl
  exact letW (A := .mut (.var 0) BB) (B := .mut (.var 0) BB) (.var (by csolo)) <|
    seqW
      (appW
        (pairW
          (pairW (.mutSub (.var (by csolo)) (entailsLe_of_meet (u := .top) rfl))
            (.mutSub (.var (by csolo)) (entailsLe_of_meet (u := .top) rfl)))
          (.var (by csolo)))
        (.allEV (x := 6) (b := .top) (A := .lolli (fam4 (.var 6)) .unit) (a := .var 3)
          (d_swapHalves (by decide) (by cdead) 6 7 rfl rfl rfl) (entailsLt_top rfl)))
      (.boxI (.unitI (by cdead)) ⟨LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩)

/-- The inner `withborF2`, at `D1`, binders `'e = 3`, `4`, `5`. -/
theorem d_withborM2In {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives D1 Γ withborF2 (.val (withborF2Ty mutM 3 D1.meetOfDom BB BB .unit)) :=
  withborM2_wf (Δ := D1) (c := 3) (x := 4) (y := 5)
    ⟨d1_ok, rfl, rfl, by decide, by simp [VFree], by simp [VFree], by simp [VFree],
      by simp [VFree], by simp [VFree], by simp [VFree],
      by simp [cbTy2, famTy2, VFree, CFree, Lifetime.Life.mentions, LifeCtx.meetOfDom,
        Lifetime.meetOfDomL, LifeCtx.empty, LifeCtx.extend],
      by simp [cbTy2, famTy2, VFree, CFree, Lifetime.Life.mentions, LifeCtx.meetOfDom,
        Lifetime.meetOfDomL, LifeCtx.empty, LifeCtx.extend], rfl⟩
    ⟨.top, LifeCtx.defines_of_wf rfl, outlives_of_dataB rfl⟩ (outlives_of_dataB rfl) .unit hΓ

/-- `(Ref B ⊗ Ref B) ⊗ 1`, the outer family's result. -/
abbrev T4 : VTy := .tensor (refs2 BB BB) .unit

theorem d_outerCb {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {S₁ : VTy} :
    CDerives LifeCtx.empty (⟨refs2 BB BB, true⟩ :: ⟨S₁, false⟩ :: Γ) outerCb
      (.val (cbTy2 mutM 0 LifeCtx.empty.meetOfDom BB BB T4)) := by
  refine .thunkV rfl (.allI (S := .unit) rfl
    (fun _ _ h => ok_empty.bound_mentions_false rfl h) ?_ (.ret (.lamV ?_)))
  · intro t ht hl
    simp only [List.mem_cons] at ht
    rcases ht with rfl | rfl | ht
    · simp [VFree]
    · simp at hl
    · exact dead_noLive hΓ (P := fun t => ¬ VFree 0 t.ty) t ht hl
  exact letW (A := refs2 BB BB) (B := .unit)
      (appW (d_innerCb (by cdead)) (appW (.var (by csolo)) (d_withborM2In (by cdead)))) <|
    .boxI (pairW (.var (by csolo)) (.var (by csolo)))
      (outlives_two (LifeCtx.defines_of_wf rfl) .unit
        (.tensor (.ref (outlives_of_dataB rfl)) (.ref (outlives_of_dataB rfl))) (by cdead))

/-- The outer `withborF2`, at `∅`, with result `(Ref B ⊗ Ref B) ⊗ 1`. -/
theorem d_withborM2Out {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ withborF2
      (.val (withborF2Ty mutM 0 LifeCtx.empty.meetOfDom BB BB T4)) :=
  withborM2_wf (famSide0 (A := BB) mutM T4 (fun _ h => by simp [VFree] at h)
      (fun _ h => by simp [VFree] at h) (fun _ _ _ => Iff.rfl) rfl)
    ⟨.top, LifeCtx.defines_of_wf rfl, outlives_of_dataB rfl⟩ (outlives_of_dataB rfl)
    (.tensor (.tensor (.ref (outlives_of_dataB rfl)) (.ref (outlives_of_dataB rfl))) .unit) hΓ

theorem d_freePair {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ (⟨refs2 BB BB, true⟩ :: Γ) (freePair 0) (.val .unit) :=
  letW (A := .ref BB) (B := .ref BB) (.var (by csolo)) <|
    seqW (d_dropB (appW (.var (by csolo)) (.free (by cdead))) (by cdead))
      (d_dropB (appW (.var (by csolo)) (.free (by cdead))) (by cdead))

theorem d_splitFour : CDerives LifeCtx.empty [] splitFour (.val .unit) :=
  letW (A := refs2 BB BB) (B := refs2 BB BB)
    (pairW
      (pairW (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead)))
        (appW (.sumI₂ (.unitI (by cdead))) (.alloc (by cdead))))
      (pairW (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead)))
        (appW (.sumI₂ (.unitI (by cdead))) (.alloc (by cdead))))) <|
  letW (A := refs2 BB BB) (B := T4)
    (appW (d_outerCb (by cdead)) (appW (.var (by csolo)) (d_withborM2Out (by cdead)))) <|
  letW (A := refs2 BB BB) (B := .unit) (.var (by csolo)) <|
  seqW (.var (by csolo)) <|
  seqW
    (letW (A := .ref BB) (B := .ref BB) (.var (by csolo)) <|
      seqW (d_dropB (appW (.var (by csolo)) (.free (by cdead))) (by cdead))
        (d_dropB (appW (.var (by csolo)) (.free (by cdead))) (by cdead)))
    (letW (A := .ref BB) (B := .ref BB) (.var (by csolo)) <|
      seqW (d_dropB (appW (.var (by csolo)) (.free (by cdead))) (by cdead))
        (d_dropB (appW (.var (by csolo)) (.free (by cdead))) (by cdead)))

theorem splitFour_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem splitFour Adequacy.emptyMem (.val .unit) :=
  adequacyC (.ret d_splitFour)

theorem splitFour_eval : unitNoLeak (eval splitFour) = true := by decide

/-- Each half swapped in place: `((inj₂, inj₁), (inj₂, inj₁))` from `((inj₁, inj₂), (inj₁, inj₂))`. -/
theorem splitFourObs_eval :
    (match eval splitFourObs with
      | .value ⟨.pair (.pair (.inj₂ .unit) (.inj₁ .unit)) (.pair (.inj₂ .unit) (.inj₁ .unit)), _⟩
          false => true
      | _ => false) = true := by decide

end BoCa.Fig16.LogRel.Core

end
